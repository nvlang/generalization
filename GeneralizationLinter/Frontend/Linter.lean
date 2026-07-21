/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
module

public import Mathlib.Lean.Elab.InfoTree
public import Lean.Linter.Basic
public import GeneralizationLinter.Core.Verify
public import GeneralizationLinter.Core.Recompile
public import GeneralizationLinter.Core.UniverseGen
public import GeneralizationLinter.Helpers.GraphCache
public import GeneralizationLinter.Core.Options

open Lean Meta Elab Command Linter Term
open GeneralizationLinter

namespace GeneralizationLinter.Frontend

/-!
# Linter




## Main definitions

* `linter`: This is the structure that gets registered via `initialize addLinter linter`, and whose
  `linter.run` function runs for every

-/

/--
Returns true if `type` has ≥1 binders that are targeted by the typeclass linter (under the given
configuration).
-/
private def hasTargetedClassBinder (type : Expr) : MetaM Bool := do
  let opts ← getOptions
  let implicit := opts.getBool ``generalizeTypeclasses.targetImplicit (defVal := true)
  let rec go : Expr → MetaM Bool
    | .forallE _ binderType body binderInfo => do
      let targeted := binderInfo.isInstImplicit ||
        (implicit && binderInfo matches .implicit | .strictImplicit)
      if targeted && (← isClass? binderType).isSome then return true else go body
    | _ => return false
  go type

/-- Helper to pretty-print a candidate. -/
private def binderDisplay (const : ConstantInfo) (c : Candidate) : MetaM String :=
  targetedBinderTelescope const.type fun lds _ => do
    match lds[c.binder.idx]? with
    | some ld => return toString (← Meta.ppExpr (← whnf ld.type))
    -- Should be unreachable.
    | none => return if c.binder.origName.isAnonymous then s!"⟨binder {c.binder.idx}⟩" else toString c.binder.origName

/-- Helper to pretty-print a targeted binder. -/
public def classBinderBracket : BinderInfo → String → String
  | .strictImplicit, s => s!"⦃{s}⦄"
  | .implicit, s => "{" ++ s ++ "}"
  | _, s => s!"[{s}]"

/-- Helper to print suggestion according to candidate's `WeakeningShape`. -/
private def describeTarget (c : Candidate) : String :=
  match c.shape with
  | .drop => "removed (dropped)"
  | .weaken t => s!"weakened to `{t.toVertex.name}`"
  | .split ts => "split into " ++
      ", ".intercalate (ts.toList.map (fun t => s!"`{t.toVertex.name}`"))

/-- Run `x` with options `opts` added to the context, and catch runtime exceptions. -/
private def withEffectiveContext (opts : Options) (heartbeats : Nat) (x : TermElabM Unit) :
    TermElabM Unit :=
  withOptions (fun _ => opts) <|
    withTheReader Core.Context (fun c => { c with maxHeartbeats := heartbeats }) <|
      tryCatchRuntimeEx x (fun _ => pure ())

/-- TODO -/
private def withDeclBudget {α : Type} (budget : Nat) (dflt : α) (x : TermElabM α) :
    TermElabM α := do
  if budget == 0 then return ← x
  let ambient := (← readThe Core.Context).maxHeartbeats
  let effectiveMax := if ambient == 0 then budget else min budget ambient
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxHeartbeats := effectiveMax })
      (withCurrHeartbeats x))
    (fun _ => pure dflt)

/-- TODO -/
private def wrapperEffectiveOptions? (wrappers : Array Syntax) :
    Command.CommandElabM (Option Options) := do
  let savedInfo ← getInfoState
  let effectiveOpts ← foldSetOptionWrappers? wrappers (← getOptions) fun opts w =>
    try
      let o ← Command.withScope (fun s => { s with opts })
        (Elab.elabSetOption (w.getArg 1) (w.getArg 3))
      pure (some o.1)
    catch _ => pure none
  setInfoState savedInfo
  return effectiveOpts

/-- TODO -/
private def lintTypeclassesFor (cfg : LinterConfig) (graph : ClassGraph) (const : ConstantInfo)
    (bodyStx : Syntax) (declName : Name) : TermElabM Unit := do
  for gw in ← withDeclBudget cfg.perDeclHeartbeats #[] (gradedWeakenings cfg graph const bodyStx) do
    let c := gw.candidate
    let disp := classBinderBracket c.binder.binderInfo (← binderDisplay const c)
    let msg := match gw.grade with
      | .proofIntact =>
        m!"the `{disp}` hypothesis of `{declName}` can be {describeTarget c}."
      | .needsModification =>
        m!"the `{disp}` hypothesis of `{declName}` can be {describeTarget c}, but the proof would have to be modified."
      -- For experiments only.
      | .unverified =>
        m!"[UNVERIFIED] the `{disp}` hypothesis of `{declName}` can be {describeTarget c}."
    logLint linter.generalizeTypeclasses (← getRef) msg

/-- TODO -/
private def lintUniversesFor (cfg : LinterConfig) (const : ConstantInfo)
    (declCmd bodyStx : Syntax) (wrappers : Array Syntax) (declName : Name) : TermElabM Unit := do
  let some declSig := declCmd.find? (·.isOfKind ``Parser.Command.declSig) | return
  let mut failed : Array PinnedBinder := #[]
  for b in ← withDeclBudget cfg.perDeclHeartbeats #[] (pinnedTypeBinders const.type) do
    if (← withDeclBudget cfg.perDeclHeartbeats none
        (universeGeneralization? const declSig bodyStx b wrappers)).isSome then
      let cur := if b.level == 1 then "Type" else s!"Type {b.level - 1}"
      logLint linter.generalizeUniverses (← getRef)
        -- TODO: Is this the right message format? I'm confused.
        m!"the `({b.name} : {cur})` binder of `{declName}` can be universe-polymorphic"
    else
      failed := failed.push b
  for lvl in (failed.map (·.level)).toList.eraseDups do
    let grp := failed.filter (·.level == lvl)
    if let some (sub, _) ← sharedSubsetLadder? grp (fun sub =>
        withDeclBudget cfg.perDeclHeartbeats none
          (universeGeneralizationsBlocks? const declSig bodyStx #[sub] wrappers)) then
      let names := ", ".intercalate (sub.toList.map fun b => s!"`{b.name}`")
      logLint linter.generalizeUniverses (← getRef)
        m!"the binders {names} of `{declName}` can be jointly universe-polymorphic at one shared level."

/--

---
**Example**

Suppose a file contains the following commands:

```
set_option A true in
open B in
set_option C true in
lemma something ‹binders› : ‹concl› := ‹value›
```

1. Lean calls `elabCommandTopLevel` on `set_option A true in`
2. , which then recursively e

-/
public def linter : Linter where
  -- `withSetOptionIn` peels off leading `set_option … in` commands
  run := withSetOptionIn fun stx => do
    let some (wrappers, declCmd) := peelWrappers? stx | return
    let some effectiveOpts ← wrapperEffectiveOptions? wrappers | return
    let lintOpts ← Command.withScope (fun s => { s with opts := effectiveOpts }) getLinterOptions
    let tcOn := getLinterValue linter.generalizeTypeclasses lintOpts
    let uvOn := getLinterValue linter.generalizeUniverses lintOpts
    unless tcOn || uvOn do return
    let hb := Core.getMaxHeartbeats effectiveOpts
    let cfg := linterConfigOfOptions effectiveOpts
    let declVals := declValNodes declCmd
    for t in ← getInfoTrees do
      let thms := t.getTheorems (← getEnv)
      unless thms.isEmpty do liftTermElabM <| withEffectiveContext effectiveOpts hb do
        let some rawBody ← (
            if declVals.size == 1 && thms.length == 1 then
              bodyTermOfDeclVal? declVals[0]! (wrapped := !wrappers.isEmpty)
            else
              pure none
          ) | return
        let bodyStx := rewrapTerm wrappers rawBody
        let graph? ← if tcOn then some <$> cachedClassGraph else pure none
        for thm in thms do
          let const ← getConstInfo thm.name
          if let some graph := graph? then
            if ← hasTargetedClassBinder const.type then
              lintTypeclassesFor cfg graph const bodyStx thm.name
          if uvOn then
            lintUniversesFor cfg const declCmd bodyStx wrappers thm.name

initialize addLinter linter
