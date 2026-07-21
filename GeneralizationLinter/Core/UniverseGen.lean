/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
module

public import GeneralizationLinter.Core.Recompile
open Lean Meta Elab Term
open Std (HashMap)

namespace GeneralizationLinter

public structure PinnedBinder where
  pos : Nat
  name : Name
  level : Nat
deriving Inhabited

public def pinnedTypeBinders (type : Expr) : MetaM (Array PinnedBinder) :=
  forallTelescope type fun xs _ => do
    let mut out := #[]
    for h : i in [0:xs.size] do
      let d ← xs[i].fvarId!.getDecl
      if let .sort l := d.type then
        if let some k := l.toNat then
          if k ≥ 1 then out := out.push ⟨i, d.userName, k⟩
    return out

private def freshLevelParams (taken : List Name) (n : Nat) : Array Name := Id.run do
  let mut acc : Array Name := #[]
  let mut taken := taken
  for _ in [0:n] do
    let u := ((List.range 1001).findSome? fun i =>
      let c := if i == 0 then `u_gl else Name.mkSimple s!"u_gl{i}"
      if taken.contains c then none else some c).getD `u_gl_fresh
    acc := acc.push u
    taken := u :: taken
  return acc

private def editedGroup? (g : Syntax) (tyNode : Syntax) : Option Syntax := do
  unless g.getKind == ``Parser.Term.explicitBinder || g.getKind == ``Parser.Term.implicitBinder
      || g.getKind == ``Parser.Term.strictImplicitBinder do failure
  if g.getKind == ``Parser.Term.explicitBinder && !(g.getArg 3).getArgs.isEmpty then failure
  let ids := (g.getArg 1).getArgs
  unless ids.size == 1 && ids[0]!.isIdent do failure
  let tySpec := g.getArg 2
  unless tySpec.getArgs.size ≥ 2 do failure
  return g.setArg 2 (tySpec.setArg 1 tyNode)

private def generalizedSigStx? (declSig : Syntax) (edits : Array (Name × Syntax)) : Option Syntax := do
  let concl := (declSig.getArg 1).getArg 1
  let mut hits := 0
  let mut binders : Array Syntax := #[]
  for g in (declSig.getArg 0).getArgs do
    let names := (g.getArg 1).getArgs.filterMap fun s => if s.isIdent then some s.getId else none
    match edits.filter (fun (n, _) => names.contains n) with
    | #[] => binders := binders.push g
    | #[(_, ty)] =>
      hits := hits + 1
      binders := binders.push (← editedGroup? g ty)
    | _ => failure
  if hits != edits.size || binders.isEmpty then failure
  return mkNode ``Parser.Term.forall
    #[mkAtom "∀", mkNullNode binders, mkNullNode #[], mkAtom ",", concl]

public structure UniverseGeneralizations where
  blocks : Array (Array PinnedBinder)
  statement : Expr
  params : Array Name
deriving Inhabited

public def universeGeneralizationsBlocks? (const : ConstantInfo) (declSig : Syntax)
    (bodyStx : Syntax) (blocks : Array (Array PinnedBinder)) (wrappers : Array Syntax := #[]) :
    TermElabM (Option UniverseGeneralizations) := do
  let bs := blocks.flatten
  if bs.isEmpty || blocks.any (·.isEmpty) then return none
  unless blocks.all (fun block => block.all (·.level == block[0]!.level)) do return none
  let unique ← forallTelescope const.type fun xs _ => do
    let mut counts : HashMap Name Nat := {}
    for x in xs do
      let n := (← x.fvarId!.getDecl).userName
      counts := counts.insert n (counts.getD n 0 + 1)
    pure (bs.all fun b => counts.getD b.name 0 == 1)
  unless unique && (bs.map (·.pos)).toList.Nodup do return none
  let us := freshLevelParams const.levelParams blocks.size
  let mut edits : Array (Name × Syntax) := #[]
  for (block, u) in blocks.zip us do
    let .ok ty := Parser.runParserCategory (← getEnv) `term s!"Type {u}" | return none
    for b in block do
      edits := edits.push (b.name, ty)
  let some sigCore := generalizedSigStx? declSig edits
    | return none
  let sigStx := rewrapTerm wrappers sigCore
  suppressingDiagnostics do try
    withLevelNames (const.levelParams ++ us.toList) do
      let W ← Term.elabType sigStx
      Term.synthesizeSyntheticMVarsNoPostponing
      let W ← instantiateMVars W
      if W.hasSorry || W.hasExprMVar || W.hasLevelMVar then return none
      let W0 := W.instantiateLevelParams us.toList
        (blocks.map (fun block => Level.ofNat (block[0]!.level - 1))).toList
      let pw := (collectLevelParams {} W0).params.toList
      let pt := const.levelParams
      let faithful ← withoutModifyingState do
        let W0 := W0.instantiateLevelParams pw (← pw.mapM fun _ => mkFreshLevelMVar)
        let T := const.type.instantiateLevelParams pt (← pt.mapM fun _ => mkFreshLevelMVar)
        isDefEq W0 T
      unless faithful do return none
      let some pf ← recompiledAgainst? W bodyStx | return none
      if (pf.find? (·.isConstOf const.name)).isSome then return none
      return some ⟨blocks, W, us⟩
  catch _ => return none

public def universeGeneralizations? (const : ConstantInfo) (declSig : Syntax) (bodyStx : Syntax)
    (bs : Array PinnedBinder) (wrappers : Array Syntax := #[]) :
    TermElabM (Option UniverseGeneralizations) :=
  universeGeneralizationsBlocks? const declSig bodyStx (bs.map (#[·])) wrappers

public def universeGeneralization? (const : ConstantInfo) (declSig : Syntax) (bodyStx : Syntax)
    (b : PinnedBinder) (wrappers : Array Syntax := #[]) :
    TermElabM (Option UniverseGeneralizations) :=
  universeGeneralizations? const declSig bodyStx #[b] wrappers

public def sharedSubsetLadder? {α : Type} (grp : Array PinnedBinder)
    (gate : Array PinnedBinder → TermElabM (Option α)) :
    TermElabM (Option (Array PinnedBinder × α)) := do
  let base := grp.take 4
  let n := base.size
  if n < 2 then return none
  let mut subsets : Array (Array PinnedBinder) := #[]
  for mask in [1:2^n] do
    let sub := (List.range n).filterMap fun i =>
      if mask.testBit i then some base[i]! else none
    if sub.length ≥ 2 then subsets := subsets.push sub.toArray
  for sub in subsets.qsort (·.size > ·.size) do
    if let some r ← gate sub then return some (sub, r)
  return none
