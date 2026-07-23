/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
module

public import GeneralizationLinter.Core.Suggest
open Lean Meta
open Std (HashMap HashSet)

namespace GeneralizationLinter

/-!
# Re-synthesize weakened binders
-/

/-- Wrapper around `reifyClass` that adds support for family class binders. -/
def replaceBinderType (oldType : Expr) (replacement : Key) : MetaM (Option Expr) := do
  -- If `oldType` reduces to a family binder `∀ prefixes, body` (where `body` is a class
  -- application), then deconstruct (i.e., telescope) `oldType`, reify the replacement class in
  -- `body`, and reconstruct (`mkForallFVars`) the family binder with the new body `body'`.
  let replVertex := replacement.toVertex
  let replName := replVertex.name
  if (← whnfR oldType).isForall then
    forallTelescopeReducing oldType fun prefixes body => do
      let some body' ← reifyClass replName (← frameArgs body) | return none
      some <$> mkForallFVars prefixes body'
  -- If `oldType` doesn't reduce to a family binder, then it's a class application.
  else do
    let oldKey ← toKey oldType
    let replPattern := replVertex.pattern
    if replPattern.any (·.looseBVarRange > oldKey.subst.size) then return none
    let mut entries : Array Expr := #[]
    for p in replPattern do
      let some e ← elabEntry (p.instantiate oldKey.subst) | return none
      entries := entries.push e
    reifyClass replName entries (useKeySlots := true)

/-- Does `e` have any fvar that is contained in `stale`? -/
def mentions (stale : HashSet FVarId) (e : Expr) : Bool :=
  e.hasAnyFVar stale.contains

mutual
/--
TODO

Arguments:
* `remap : HashMap FVarId Expr`: Map from old binders to new binders. Note that all binders are
  included here, even non-targeted binders.
* `stale`:
-/
private partial def reSynthExpr (remap : HashMap FVarId Expr) (stale staleW : HashSet FVarId) (e : Expr) :
    MetaM Expr := do
  match e with
  -- fvars are remapped according to `remap`, or left as-is if they're not in `remap`.
  | .fvar fvarId => return remap.getD fvarId e

  -- Application (`fn a₁ … aₙ`) ⟹ Rebuild head and arguments.
  | .app .. => e.withApp fun fn args => do
      return mkAppN (← reSynthExpr remap stale staleW fn) (← args.mapM (reSynthArg remap stale staleW))

  -- Anonymous function (``fun `name : type => body``) ⟹
  -- 1. Rebuild `type` into `type'`
  -- 2. Temporarily add local declaration `x : type'` to context, where `x` is an fvar of type
  --    `type'` with user-facing name `` `name ``. Note that `x` inherits the original binder info
  --    (e.g., `.default`, `.implicit`, etc.), and that, if `x` is class-typed (i.e., if `type'` is
  --    a class application), then `x` is registered as an instance in our transient local context,
  --    which is relevant for any synthesis that may occur while rebuilding `body` in step
  --    3.
  -- 3. Instantiate `bvar 0` in `body` to the fvar `x` from step 2, and rebuild the result to get
  --    `body'`.
  -- 4. Construct an anonymous function using `x` and `body'`, revert the local context, and return
  --    the constructed anonymous function.
  | .lam binderName binderType body binderInfo =>
    let binderType' ← if mentions stale binderType then
      reSynthExpr remap stale staleW binderType else pure binderType
    withLocalDecl binderName binderInfo binderType' fun x => do
      mkLambdaFVars #[x] (← reSynthExpr remap stale staleW (body.instantiate1 x))

  -- Forall-expression / dependent arrow (``forall `name : type, body``) ⟹ Basically the same
  -- treatment as anonymous functions, except that the constructed expression is a forall-expression
  -- instead of an anonymous function.
  | .forallE binderName binderType body binderInfo =>
    let binderType' ← if mentions stale binderType then
      reSynthExpr remap stale staleW binderType else pure binderType
    withLocalDecl binderName binderInfo binderType' fun x => do
      mkForallFVars #[x] (← reSynthExpr remap stale staleW (body.instantiate1 x))

  -- Let-expression (``let `name : type := value; body``) ⟹ Basically the same treatment as
  -- anonymous functions, except that the constructed expression is a let-expression instead of an
  -- anonymous function, and that the `LocalDecl` temporarily added to the context is a
  -- `LocalDecl.ldecl`, meaning that it has a value, unlike the `LocalDecl` added by `withLocalDecl`
  -- in the `.lam` and `.forallE` branches, which adds a `LocalDecl.cdecl` to the context, which is
  -- opaque and doesn't have a value.
  | .letE declName type value body _ =>
    let type' ← if mentions stale type then reSynthExpr remap stale staleW type else pure type
    withLetDecl declName type' (← reSynthArg remap stale staleW value) fun x => do
        mkLetFVars #[x] (← reSynthExpr remap stale staleW (body.instantiate1 x))

  -- If the expression is just a subexpression wrapped with metadata, recurse into the subexpression.
  | .mdata data expr => return .mdata data (← reSynthExpr remap stale staleW expr)

  -- Projection-expression (e.g. `struct.2`, where `struct : Int × Int`) ⟹ Recurse into `struct`.
  -- Note that field accesses reduce to projection-expressions.
  | .proj typeName idx struct =>
    if ¬ mentions stale struct then return e
    let struct' ← reSynthArg remap stale staleW struct
    let raw : Expr := .proj typeName idx struct'
    let structType ← whnf (← inferType struct')
    if structType.getAppFn.isConstOf typeName then
      return raw
    else
      let some info := getStructureInfo? (← getEnv) typeName | return raw
      let some fieldName := info.fieldNames[idx]? | return raw
      try mkProjection struct' fieldName catch _ => return raw

  -- The remaining expressions can't contain any fvars to remap or instances to resynthesize, so we
  -- return them as they are.
  | .const .. | .sort .. | .lit .. | .bvar .. | .mvar .. => return e

/-- Rebuild an application argument. -/
private partial def reSynthArg (remap : HashMap FVarId Expr) (stale staleW : HashSet FVarId) (arg : Expr) :
    MetaM Expr := do
  -- If `arg` doesn't mention _any_ stale fvars, we just return it as is; nothing to update.
  unless mentions stale arg do return arg
  -- If `arg` doesn't mention any weakened binders, we just need to remap the fvars (which
  -- `reSynthExpr` will do for us), but don't have to (and in fact shouldn't) try to re-synthesize
  -- `arg` or anything within it.
  unless mentions staleW arg do return ← reSynthExpr remap stale staleW arg
  -- `arg` mentions a weakened binder. TODO: Understand this in-depth.
  let fallback : MetaM Expr := do
    if let .const declName us := arg.getAppFn then
      if declName.isInternal then
        if let some info := (← getEnv).find? declName then
          if let some v := info.value? (allowOpaque := true) then
            return ← reSynthArg remap stale staleW
              ((v.instantiateLevelParams info.levelParams us).beta arg.getAppArgs)
    reSynthExpr remap stale staleW arg
  -- Infer type of `arg`, defaulting to `Sort 0` if we can't (should be unreachable though).
  let type ← (try instantiateMVars (← inferType arg) catch _ => pure (.sort .zero))
  -- TODO: Understand the below (it's changed).
  if (← isClass? type).isSome then
    let trySynth (goal : Expr) : MetaM Expr := do
      match ← (try trySynthInstance goal catch _ => pure .none) with
      | .some inst =>
        let inst ← instantiateMVars inst
        if inst.hasExprMVar || mentions stale inst then fallback else return inst
      | _ => fallback
    if mentions stale type then
      let type' ← reSynthExpr remap stale staleW type
      if ¬ mentions stale type' then trySynth type' else fallback
    else
      trySynth type
  else
    fallback
end


/--
Rebuild each element of `rest = [b₁, …, bₙ]`, where `bᵢ` is the `i`th binder after the targeted
binder in the original declaration's telescope. Binder `bᵢ` gets rebuilt with all of the rebuilt
binders `b₁, …, bᵢ₋₁` added to the context.

Afterwards, run continuation `k`.

The arguments `stale` and `staleW` are passed as-is to `reSynthExpr` during the rebuilding, and
never modified. The argument `remap` is extended with the mappings `b₁ ↦ b₁', …, bₙ ↦ bₙ'`, where
`bᵢ'` is the rebuilt version of `bᵢ`.
-/
private partial def reSynthTelescope {α : Type} (remap : HashMap FVarId Expr)
    (stale staleW : HashSet FVarId) (rest : List Expr)
    (k : HashMap FVarId Expr → Array Expr → MetaM α) : MetaM α := do
  go remap rest #[]
where
  /--
  * `remap` contains `b₁ ↦ b₁', …, bₖ ↦ bₖ'`, where `bᵢ'` is the rebuilt version of `bᵢ`.
    It also contains whatever `reSynthTelescope`'s caller passed it with.
  * `rest` contains the remaining binders to be rebuilt, `[bₖ₊₁, …, bₙ]`.
  * `newBinders` contains new binders built thus far, `#[b₁', …, bₖ']`.
  -/
  go (remap : HashMap FVarId Expr) (rest : List Expr) (newBinders : Array Expr) : MetaM α := do
    match rest with
    | [] => k remap newBinders
    | x :: rest => do
      let ld ← x.fvarId!.getDecl
      let type ← instantiateMVars ld.type
      let type' ← if mentions stale type then reSynthExpr remap stale staleW type else pure type
      withLocalDecl ld.userName ld.binderInfo type' fun xNew => do
        let remap' := remap.insert x.fvarId! xNew
        go remap' rest (newBinders.push xNew)


/--
Among an array `fvars` of `.fvar` expressions, find the `n`th entry that corresponds to a
`TargetedBinder`. This checks the local context to see how each fvar in `fvars` was declared, and
returns `some i binder` if the `n`th targeted binder is the fvar `binder`, and `binder = fvars[i]`.
It returns `none` if there is no `n`th targeted binder in `fvars`.
-/
public def getNthTargetedBinder (fvars : Array Expr) (n : Nat) : MetaM (Option (Nat × Expr)) := do
  let mut clsIdx := 0
  for h : i in [0:fvars.size] do
    if ← isTargetedBinder (← fvars[i].fvarId!.getDecl) then
      if clsIdx == n then return some (i, fvars[i])
      clsIdx := clsIdx + 1
  return none


/--
Remove the local instance with `FVarId` `drop` from the context, run `act`, then restore the
context.
-/
def withoutLocalInstance {α : Type} (drop : FVarId) (act : MetaM α) : MetaM α :=
  withReader (fun ctx => { ctx with
    localInstances := ctx.localInstances.filter (·.fvar.fvarId! != drop) }) act

/-- TODO -/
public def replacementsRedundant (type : Expr) (binderIdx : Nat) (repls : Array Key) :
    MetaM Bool := do
  try
    forallTelescope type fun args _ => do
      let some (_, fv) ← getNthTargetedBinder args binderIdx | return false
      let oldType ← inferType fv
      let mut goals : Array Expr := #[]
      for r in repls do
        let some g ← replaceBinderType oldType r | return none |>.getD false
        goals := goals.push g
      withoutLocalInstance fv.fvarId! <| goals.allM fun g => return (← synthInstance? g).isSome
  catch _ => return false


/--
Replace the targeted binder `tb` with `replacements`. If `replacements` is empty, this means
dropping `tb`. If `replacements` has more than one element, this means splitting `tb` up into
multiple binders.

Parameters:
* `tb`: `FVarId` of targeted binder that is to be replaced.
* `replacements`: The `Name`s of the class heads to replace `tb`'s type with.
* `k`: Continuation, which receives
  * If `replacements` is empty or `replacements.size ≥ 2`, then an empty map. If `replacements.size
    == 1`, then a map from `tb` to `replacements[0]`.
  * The array of new replacement binder `Expr`s that were built.
-/
def withReplacementBinders {α : Type} (tb : FVarId) (replacements : Array Key)
    (k : HashMap FVarId Expr → Array Expr → MetaM (Option α)) : MetaM (Option α) := do
  let oldDecl ← tb.getDecl
  let userName := oldDecl.userName
  let rec go (i : Nat) (remap : HashMap FVarId Expr) (newBinders : Array Expr) : MetaM (Option α) := do
    if h : i < replacements.size then
      let some newBinderType ← replaceBinderType (← tb.getType) replacements[i] | return none
      withLocalDecl userName oldDecl.binderInfo newBinderType fun newBinder => do
        withNewLocalInstance ((← isClass? newBinderType).getD replacements[i].toVertex.name) newBinder
          (go (i + 1) (if replacements.size == 1 then remap.insert tb newBinder else remap)
            (newBinders.push newBinder))
    else k remap newBinders
  go 0 {} #[]

def staleSets (oldFV : FVarId) (post : Array Expr) : HashSet FVarId × HashSet FVarId :=
  let staleW := {oldFV}
  (staleW, post.foldl (init := staleW) (·.insert ·.fvarId!))

-- /--
-- TODO (Cascade.lean)
--
-- Note: Currently unused, used for cascade in different branch.
-- -/
-- public def rebuildWeakenedProof (value : Expr) (n : Nat) (replacements : Array Name) :
--     MetaM (Option (Expr × Expr)) := do
--   if replacements.size > 1 then return none -- splits are not this function's responsibility
--   forallTelescope (← inferType value) fun args _ => do
--     let body ← Core.betaReduce (mkAppN value args)
--     let some (targetedIdx, oldBinder) ← getNthTargetedBinder args n | return none
--     let oldFV := oldBinder.fvarId!
--     let pre := args[0:targetedIdx].toArray
--     let post := (args[targetedIdx+1:args.size]).toArray
--     let (staleW, stale) := staleSets oldFV post
--     let close : Array Expr → Expr → MetaM (Option (Expr × Expr)) := fun binders body' => do
--       try
--         let value' ← instantiateMVars (← mkLambdaFVars binders body')
--         if value'.hasExprMVar || value'.hasSorry then return none
--         if mentions stale value' then return none
--         Meta.check value'
--         return some ((← instantiateMVars (← inferType value')), value')
--       catch _ => return none
--     withReplacementBinders oldFV replacements fun remap newBinders =>
--       withoutLocalInstance oldFV do
--         reSynthTelescope remap stale staleW post.toList fun remap rebuiltPost => do
--           let body' ← reSynthArg remap stale staleW body
--           close (pre ++ newBinders ++ rebuiltPost) body'


/--
TODO
-/
public def verifyWeakening (ciType val : Expr) (k : Nat) (repls : Array Key) : MetaM Bool := do
  forallTelescope ciType fun args concl => do
    let body ← Core.betaReduce (mkAppN val args)
    let some (ti, oldBinder) ← getNthTargetedBinder args k | return false
    let oldFV := oldBinder.fvarId!
    let post := (args[ti+1:args.size]).toArray
    let (staleW, stale) := staleSets oldFV post
    let finish (sub0 : HashMap FVarId Expr) (newBinders : Array Expr) : MetaM Bool :=
      withoutLocalInstance oldFV do
        reSynthTelescope sub0 stale staleW post.toList fun remap rebuiltPost => do
          let body' ← reSynthArg remap stale staleW body
          let concl' ← reSynthExpr remap stale staleW concl
          if mentions stale body' || mentions stale concl' then return false
          try
            if body'.hasExprMVar || body'.hasSorry then return false
            let concl' ← instantiateMVars concl'
            Meta.check concl'
            if concl'.hasExprMVar || concl'.hasSorry then return false
            let W ← instantiateMVars
              (← mkForallFVars (args[0:ti].toArray ++ newBinders ++ rebuiltPost) concl')
            if W.hasLooseBVars || mentions stale W then
              return false
            Meta.check W
            Meta.check body'
            let bty ← instantiateMVars (← inferType body')
            isDefEq bty concl'
          catch _ => return false
    return (← withReplacementBinders oldFV repls fun remap newBinders =>
      some <$> finish remap newBinders).getD false

-- /--
-- Given a name `name` and its associated constant info `const`, returns the head of the class-typed
-- conclusion of `const` if `const` could be a vacuity witness, and `none` otherwise.

-- ---
-- **Implementation notes**

-- If `name` refers to a constant `const` for which we have that

-- 1.  `const` is a definition (not a theorem, axiom, etc.),
-- 2.  `const` is not internal (i.e., `name` does not start with `_`),
-- 3.  `const`'s binders are all instance-implicit or `Sort`-typed,
-- 4.  `const` has at least one class premise, and
-- 5.  `const` concludes in a class application,

-- then we view `const` as a potential "vacuity witness", i.e., a definition that may show that a
-- weakening candidate is vacuous. An example of such a `const`:

-- ```
-- abbrev Module.addCommMonoidToAddCommGroup (R : Type*) {M : Type*}
--     [Ring R] [AddCommMonoid M] [Module R M] : AddCommGroup M where --
-- ```

-- The 5 conditions enumerated above are only a heuristic. They may miss definitions that could be
-- vacuity witnesses, and certainly may include ones that couldn't be. As such, we cannot guarantee
-- that no vacuous suggestions will ever be emitted, but are merely trying to minimize their frequency
-- to the point that at most a handful of vacuous weakenings are suggested across all of Mathlib, so
-- that the linter can be turned off locally for these.
-- -/
-- def vacuityWitnessHead? (env : Environment) (name : Name) (const : ConstantInfo) : Option Name :=
--   if !(const matches .defnInfo _) || name.isInternal then none else go const.type false
-- where
--   go : Expr → Bool → Option Name
--     -- Work through binders one by one.
--     | .forallE _ binderType body binderInfo, hasPremise =>
--       -- We assume all instance-implicit arguments are class-typed.
--       if binderInfo == .instImplicit then go body true
--       else if binderType.isSort then go body hasPremise
--       -- ≥1 of the binders is neither instance-implicit nor `Sort`-typed ⟹ `const` is not a vacuity
--       -- witness according to our heuristic (condition 3).
--       else none
--     -- Base case: If we've made it to here, we just need to check that `const`'s conclusion is
--     -- indeed class-typed, and then we can return its head.
--     | e, hasPremise => do
--       guard hasPremise
--       let .const c _ := e.getAppFn | none
--       guard (isClass env c)
--       some c

-- /--
-- Scanning the environment for vacuity witnesses isn't super expensive, but it's not cheap either, so
-- we cache the scan of imported constants specifically for each process; if the imported constants
-- change, this generally requires a file rebuild, which would lead to a new process and hence kindly
-- invalidate this cache for us.
-- -/
-- private initialize witnessScanRef : IO.Ref (Option (NameMap (Array Name))) ← IO.mkRef none

-- /--
-- Return all the potential vacuity witnesses (according to `vacuityWitnessHead?`) that are defined in
-- the environment for the class `className`, but which are not registered instances (since those are
-- taken into account by #TODO already).
-- -/
-- def vacuityWitnessesFor (className : Name) : MetaM (Array Name) := do
--   let env ← getEnv
--   let instances := (instanceExtension.getState env).instanceNames
--   -- `nameMap` is the map from class names to the arrays of potential vacuity witnesses (according
--   -- to `vacuityWitnessHead?`), which we're accumulating toward. `n` is a name of a constant that
--   -- we're checking out to see whether we should add it to `nameMap`, and `const` is `n`'s constant
--   -- info.
--   let add (nameMap : NameMap (Array Name)) (n : Name) (const : ConstantInfo) : NameMap (Array Name) :=
--     match vacuityWitnessHead? env n const with
--     | some vacWitnessHead =>
--       if instances.contains n then
--         nameMap -- Registered instance already
--       else
--         nameMap.insert vacWitnessHead ((nameMap.getD vacWitnessHead #[]).push n)
--     | none => nameMap
--   -- This is the "vacuity witness name map" for imported constants, taken from the `witnessScanRef`
--   -- cache or, if called for the first time, built from scratch.
--   let imported ← (← witnessScanRef.get).getDM do
--     let nameMap := env.constants.map₁.fold add {}
--     witnessScanRef.set (some nameMap)
--     pure nameMap
--   -- This is the "vacuity witness name map" for local constants, built from scratch on every call.
--   -- This build is very fast, since the number of local constants is generally rather small, and
--   -- almost always far smaller than the number of important constants.
--   let locals := env.constants.map₂.foldl add {}
--   -- Return potential vacuity witnesses from across both imported and local constants.
--   return (imported.getD className #[]) ++ (locals.getD className #[])


/--
TODO
-/
public def weakenedStatementType (const : ConstantInfo) (ws : Array (Nat × Array Key)) : MetaM (Option Expr) := do
  let sorted := ws.qsort (fun a b => a.1 > b.1)
  let mut type := const.type
  for (k, repls) in sorted do
    let some t ← rebuiltStatementType type k repls | return none
    type := t
  return some type
where
  rebuiltStatementType (type : Expr) (n : Nat) (repls : Array Key) : MetaM (Option Expr) := do
    forallTelescope type fun args concl => do
      let some (ti, _) ← getNthTargetedBinder args n | return none
      let oldFVar := args[ti]!.fvarId!            -- `FVarId` of targeted binder
      let pre := args[0:ti].toArray               -- binders before (i.e., to the left of) the target
      let post := (args[ti+1:args.size]).toArray  -- binders after (i.e., to the right of) the target
      let (staleW, stale) := staleSets oldFVar post
      -- TODO
      let close (remap₀ : HashMap FVarId Expr) (newBinders : Array Expr) : MetaM (Option Expr) :=
        reSynthTelescope remap₀ stale staleW post.toList fun remap rebuiltPost => do
          let concl' ← reSynthExpr remap stale staleW concl
          if mentions stale concl' then return none
          let type ← instantiateMVars (← mkForallFVars (pre ++ newBinders ++ rebuiltPost) concl')
          if type.hasLooseBVars || type.hasExprMVar || mentions stale type then return none
          unless ← isTypeCorrect type do return none
          return some type
      withReplacementBinders oldFVar repls fun remap newBinders =>
        withoutLocalInstance oldFVar (close remap newBinders)
