/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
module

public import Lean.Meta.Basic
import Lean.Meta.SynthInstance
import Lean.Structure

import Mathlib.Lean.Expr.Basic

public import GeneralizationLinter.Graph.Vertex
import GeneralizationLinter.Analysis.Collect
import GeneralizationLinter.Graph.ClassGraph

open Lean Meta
open Std (HashMap HashSet)

namespace GeneralizationLinter

/-!
# Re-synthesize weakened binders
-/

/-- The information that `reSynthExpr` and `reSynthArg` need. -/
structure ReSynthContext where
  /--
  Map from stale binders' fvars to their rebuilt expressions. The stale binders in this map are the
  targeted binder (iff it isn't being split up or dropped), and all the binders that come after it
  in the linted theorem's signature.
  -/
  remap : HashMap FVarId Expr
  /--
  Set containing the fvar of the targeted binder, and the fvars of any binders coming after the
  targeted binder.
  -/
  stale : HashSet FVarId
  /-- Set containing the fvar of the targeted binder. Note that `staleW ⊆ stale`. -/
  staleW : HashSet FVarId


/-- Context established by `withWeakenedDecl` and handed to its continuation. -/
structure WeakenedDeclContext extends ReSynthContext where
  /-- The original telescope. -/
  args : Array Expr
  /-- Binders that were introduced _before_ the target. -/
  pre : Array Expr
  /-- The binders replacing the target binder. -/
  newBinders : Array Expr
  /-- Rebuilt versions of the binders that were introduced _after_ the target. -/
  rebuiltPost : Array Expr
  /-- The original conclusion. -/
  concl : Expr

def WeakenedDeclContext.weakenedTelescope (ctx : WeakenedDeclContext) : Array Expr :=
  ctx.pre ++ ctx.newBinders ++ ctx.rebuiltPost


/-- Wrapper around `mkClassApp?` / `reifyKey?` that adds support for parametric class binders. -/
public def replaceBinderType? (oldType : Expr) (replacement : Vertex) : MetaM (Option Expr) := do
  -- If `oldType` reduces to a parametric binder `∀ prefixes, body` (where `body` is a class
  -- application), then deconstruct (i.e., telescope) `oldType`, reify the replacement class in
  -- `body`, and reconstruct (`mkForallFVars`) the parametric binder with the new body `body'`.
  if (← whnfR oldType).isForall then
    forallTelescopeReducing oldType fun prefixes body => do
      let some body' ← mkClassApp? replacement.name (← frameArgs body) | return none
      some <$> mkForallFVars prefixes body'
  -- If `oldType` doesn't reduce to a parametric binder, then it's a class application.
  else do
    let oldKey ← canonKey oldType
    reifyKey? replacement.name replacement.pattern oldKey.subst


/-- Does `e` have any fvar that is contained in `stale`? -/
def mentions (stale : HashSet FVarId) (e : Expr) : Bool :=
  e.hasAnyFVar stale.contains

mutual
/-- Rebuilds `e` into an expression that is valid in the weakened context. -/
partial def ReSynthContext.reSynthExpr (ctx : ReSynthContext) (e : Expr) :
    MetaM Expr := do
  match e with
  -- fvars are remapped according to `remap`, or left as-is if they're not in `remap`.
  | .fvar fvarId => return ctx.remap.getD fvarId e

  -- Application (`fn a₁ … aₙ`) ⟹ Rebuild head and arguments.
  | .app .. => e.withApp fun fn args => do
      return mkAppN (← ctx.reSynthExpr fn) (← args.mapM ctx.reSynthArg)

  -- Anonymous function (``fun `name : type => body``) ⟹
  -- 1. Rebuild `type` into `type'`
  -- 2. Temporarily add local declaration `x : type'` to context, where `x` is an fvar of type
  --    `type'` with user-facing name `` `name ``. Note that `x` inherits the original binder info
  --    (e.g., `.default`, `.implicit`, etc.), and that, if `x` is class-typed (i.e., if `type'` is
  --    a class application), then `x` is registered as an instance in our transient local context,
  --    which is relevant for any synthesis that may occur while rebuilding `body` in step 3.
  -- 3. Instantiate `bvar 0` in `body` to the fvar `x` from step 2, and rebuild the result to get
  --    `body'`.
  -- 4. Construct an anonymous function using `x` and `body'`, revert the local context, and return
  --    the constructed anonymous function.
  | .lam binderName binderType body binderInfo =>
    let binderType' ← if mentions ctx.stale binderType then
      ctx.reSynthExpr binderType else pure binderType
    withLocalDecl binderName binderInfo binderType' fun x => do
      mkLambdaFVars #[x] (← ctx.reSynthExpr (body.instantiate1 x))

  -- Forall-expression / dependent arrow (``forall `name : type, body``) ⟹ Basically the same
  -- treatment as anonymous functions, except that the constructed expression is a forall-expression
  -- instead of an anonymous function.
  | .forallE binderName binderType body binderInfo =>
    let binderType' ← if mentions ctx.stale binderType then
      ctx.reSynthExpr binderType else pure binderType
    withLocalDecl binderName binderInfo binderType' fun x => do
      mkForallFVars #[x] (← ctx.reSynthExpr (body.instantiate1 x))

  -- Let-expression (``let `name : type := value; body``) ⟹ Basically the same treatment as
  -- anonymous functions, except that the constructed expression is a let-expression instead of an
  -- anonymous function, and that the `LocalDecl` temporarily added to the context is a
  -- `LocalDecl.ldecl`, meaning that it has a value, unlike the `LocalDecl` added by `withLocalDecl`
  -- in the `.lam` and `.forallE` branches, which adds a `LocalDecl.cdecl` to the context, which is
  -- opaque and doesn't have a value.
  | .letE declName type value body _ =>
    let type' ← if mentions ctx.stale type then ctx.reSynthExpr type else pure type
    withLetDecl declName type' (← ctx.reSynthArg value) fun x => do
        mkLetFVars #[x] (← ctx.reSynthExpr (body.instantiate1 x))

  -- If the expression is just a subexpression wrapped with metadata, recurse into the subexpression.
  | .mdata data expr => return .mdata data (← ctx.reSynthExpr expr)

  -- Projection-expression (e.g. `struct.2`, where `struct : Int × Int`) ⟹ Recurse into `struct`.
  -- Note that field accesses reduce to projection-expressions.
  | .proj typeName idx struct =>
    if ¬ mentions ctx.stale struct then return e
    let struct' ← ctx.reSynthArg struct
    let raw : Expr := .proj typeName idx struct'
    let structType ← whnf (← inferType struct')
    if structType.getAppFn.isConstOf typeName then
      return raw
    else
      let some info := getStructureInfo? (← getEnv) typeName | return raw
      let some fieldName := info.fieldNames[idx]? | return raw
      try Expr.mkProjection struct' fieldName catch _ => return raw

  -- The remaining expressions can't contain any fvars to remap or instances to resynthesize, so we
  -- return them as they are.
  | .const .. | .sort .. | .lit .. | .bvar .. | .mvar .. => return e


/--
Rebuild an application argument.

---
**Implementation notes**

* If `arg` mentions no stale fvars, it's returned unchanged.
* If `arg` mentions stale fvars but not the weakened binder itself, we just remap it to the new fvar
  indicated by `ctx.remap`. We deliberately don't attempt any instance synthesis here.
* If `arg` mentions the weakened binder:
  * Set `fallback`:
    * If `arg` is an application headed by a constant that was dynamically generated by the
      elaborator, we unfold ("inline") it and call `reSynthArg` on the result (the β-reduced body).
    * Otherwise, we just call `reSynthExpr` on `arg`.
  * If `arg` is an instance (i.e., is class-typed):
    * If `arg`'s type mentions a stale binder, we first try to rebuild it using `reSynthExpr` and
      then synthesize a replacement for `arg` in the weakened context. If any of this fails, or if
      the newly synthesized instance contains metavariables or mentions a stale binder, we return
      `fallback`.
  * If `arg` is not an instance, return `fallback`.

---
**Example** (why unfolding dynamically generated constants is important here)

Take the following definition:

```
def MonoidHom.mk' [Group G] [MulOneClass M] (f : M → G)
    (map_mul : ∀ a b, f (a * b) = f a * f b) : M →* G where
  toFun := f
  map_mul' := map_mul
  map_one' := by rw [← mul_right_cancel_iff, ← map_mul _ 1, one_mul, one_mul]
```

Let `value` refer to the value of `MonoidHom.mk'`.

Our linter notices that, for `MonoidHom.mk'`, `Group G` can be weakened to `RightCancelMonoid G`. It
then wants to verify this weakening candidate. In this process, `weakeningResynthesizable` β-reduces
the value of `MonoidHom.mk'` applied to `MonoidHom.mk'`'s telescope. Call the result of this
β-reduction `body`. Then `weakeningResynthesizable` calls `ctx.reSynthArg body`.

> Now, for context, the elaborated value of `MonoidHom.mk'` is as follows:
>
> ```
> fun {M} {G} [inst : Group G] [inst_1 : MulOneClass M] f map_mul ↦
>   @MonoidHom.mk M G (@MulOneClass.toMulOne M inst_1)
>     (@MulOneClass.toMulOne G (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
>     (@OneHom.mk M G (@MulOne.toOne M (@MulOneClass.toMulOne M inst_1))
>       (@MulOne.toOne G
>         (@MulOneClass.toMulOne G (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst)))))
>       f (@MonoidHom.mk'._proof_1 M G inst inst_1 f map_mul))
>       -- ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
>     map_mul
> ```
>
> Note the `@MonoidHom.mk'._proof_1` in this value; that's a dynamically generated constant. And
> note how `inst` and `inst_1` are passed to it directly. Indeed, `MonoidHom.mk'._proof_1` has the
> following type:
>
> ```
> MonoidHom.mk'._proof_1 : ∀ {M G} [inst : Group G] [inst_1 : MulOneClass M] (f : M → G),
>     (∀ a b, f (a * b) = f a * f b) → f 1 = 1
> ```
>
> But that doesn't mean that it genuinely requires everything its signature says it does;
> dynamically generated constants simply define their signatures using the context within which
> they're generated, and don't check whether a weaker signature could suffice for their conclusion.
> In the `MonoidHom.mk'._proof_1` case, we have that its value happens to only need `MulOneClass M`,
> `MulOneClass G`, and `IsRightCancelMul G`; the latter two join at `RightCancelMonoid G`, so `Group
> G` could be weakened to `RightCancelMonoid G` in `MonoidHom.mk'._proof_1`'s signature.

This call `ctx.reSynthArg body` will eventually call `ctx.reSynthArg ‹@MonoidHom.mk'._proof_1 M G
inst inst_1 f map_mul›`. Now, if we didn't unfold `@MonoidHom.mk'._proof_1 M G inst inst_1 f
map_mul`, `reSynthArg` would leave the head `@MonoidHom.mk'._proof_1` as is and try to rebuild each
of its binders. In the case of `[inst : Group G]`, which reflects `MonoidHom.mk'`'s _unweakened_
signature, it would try to synthesize this within the context of `MonoidHom.mk'`'s _weakened_
signature, and fail. It would then pass the fallback to `MonoidHom.mk'._proof_1` instead. This
fallback would be `ctx.reSynthExpr ‹inst›`, which would simply consult `ctx.remap` and return the
free variable `inst'` that corresponds to the weakened binder `[inst' : RightCancelMonoid G]`. Then,
once `weakeningResynthesizable` type-checks `body'` (the badly rebuilt `body`), the check would
fail, as `inst'` does not have the type `Group G` that `MonoidHom.mk'._proof_1` requires it to have.
This in turn would make `weakeningResynthesizable` reject the weakening.

In short, unfolding the applications of these dynamically generated constants is important because
any declaration whose elaboration produces them would otherwise be falsely restricted to whatever
slice of the declaration's old signature the constants' bodies happened to mention.
-/
partial def ReSynthContext.reSynthArg (ctx : ReSynthContext) (arg : Expr) :
    MetaM Expr := do
  -- If `arg` doesn't mention _any_ stale fvars, we just return it as is; nothing to update.
  unless mentions ctx.stale arg do return arg
  -- If `arg` doesn't mention any weakened binders, we just need to remap the fvars (which
  -- `reSynthExpr` will do for us), but don't have to (and in fact shouldn't) try to re-synthesize
  -- `arg` or anything within it.
  unless mentions ctx.staleW arg do return ← ctx.reSynthExpr arg
  -- `arg` mentions a weakened binder, so it has to be rebuilt.
  let fallback : MetaM Expr := do
    if let .const declName levels := arg.getAppFn then
      -- If `arg` is an application of `declName` and `declName` was dynamically generated, unfold
      -- `arg` and call `reSynthArg` on the result.
      if declName.isInternalDetail then
        if let some info := (← getEnv).find? declName then
          if let some value := info.value? (allowOpaque := true) then
            return ← ctx.reSynthArg
              ((value.instantiateLevelParams info.levelParams levels).beta arg.getAppArgs)
    ctx.reSynthExpr arg
  -- Infer type of `arg`, defaulting to `Sort 0` if we can't (should be unreachable though).
  let type ← (try instantiateMVars (← inferType arg) catch _ => pure (.sort .zero))
  -- If `arg` is class-typed, re-synthesize it in the weakened context.
  if (← isClass? type).isSome then
    let trySynth (goal : Expr) : MetaM Expr := do
      match ← (try trySynthInstance goal catch _ => pure .none) with
      | .some inst =>
        let inst ← instantiateMVars inst
        if inst.hasExprMVar || mentions ctx.stale inst then fallback else return inst
      | _ => fallback
    if mentions ctx.stale type then
      let type' ← ctx.reSynthExpr type
      if ¬ mentions ctx.stale type' then trySynth type' else fallback
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

`ctx.stale` and `ctx.staleW` are never modified, while `ctx.remap` is extended with the mappings `b₁
↦ b₁', …, bₙ ↦ bₙ'`, where `bᵢ'` is the rebuilt version of `bᵢ`.
-/
partial def ReSynthContext.reSynthTelescope {α : Type} (ctx : ReSynthContext)
    (rest : List Expr) (k : ReSynthContext → Array Expr → MetaM α) : MetaM α := do
  go ctx rest #[]
where
  /--
  * `ctx.remap` contains `b₁ ↦ b₁', …, bₖ ↦ bₖ'`, where `bᵢ'` is the rebuilt version of `bᵢ`. It
    also contains whatever `reSynthTelescope`'s caller passed in.
  * `rest` contains the remaining binders to be rebuilt, `[bₖ₊₁, …, bₙ]`.
  * `newBinders` contains new binders built thus far, `#[b₁', …, bₖ']`.
  -/
  go (ctx : ReSynthContext) (rest : List Expr) (newBinders : Array Expr) : MetaM α := do
    match rest with
    | [] => k ctx newBinders
    | x :: rest => do
      let ld ← x.fvarId!.getDecl
      let type ← instantiateMVars ld.type
      let type' ← if mentions ctx.stale type then ctx.reSynthExpr type else pure type
      withLocalDecl ld.userName ld.binderInfo type' fun xNew => do
        go { ctx with remap := ctx.remap.insert x.fvarId! xNew } rest (newBinders.push xNew)


/--
Among an array `fvars` of `.fvar` expressions, find the `n`th entry that corresponds to a
`TargetedBinder`. This checks the local context to see how each fvar in `fvars` was declared, and
returns `some i binder` if the `n`th targeted binder is the fvar `binder`, and `binder = fvars[i]`.
It returns `none` if there is no `n`th targeted binder in `fvars`.
-/
public def getNthTargetedBinder? (fvars : Array Expr) (n : Nat) : MetaM (Option (Nat × Expr)) := do
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


/--
Returns `true` iff every `repls[i]`'s class is already synthesizable from the other binders (the ones
not being replaced).
-/
public def replacementsRedundant (type : Expr) (binderIdx : Nat) (repls : Array Vertex) :
    MetaM Bool := do
  try
    forallTelescope type fun args _ => do
      let some (_, fv) ← getNthTargetedBinder? args binderIdx | return false
      let oldType ← inferType fv
      let mut goals : Array Expr := #[]
      for r in repls do
        let some g ← replaceBinderType? oldType r | return none |>.getD false
        goals := goals.push g
      withoutLocalInstance fv.fvarId! <| goals.allM fun g => return (← synthInstance? g).isSome
  catch _ => return false


/--
Replace the targeted binder `tb` with `replacements`. If `replacements` is empty, this means
dropping `tb`. If `replacements` has more than one element, this means splitting `tb` up into
multiple binders.

Parameters:
* `tb`: `FVarId` of targeted binder that is to be replaced.
* `replacements`: The `Vertex`es with which to replace `tb`'s type.
* `k`: Continuation, which receives
  * If `replacements` is empty or `replacements.size ≥ 2`, then an empty map. If `replacements.size
    == 1`, then a map from `tb` to `replacements[0]`.
  * The array of new replacement binder `Expr`s that were built.
-/
def withReplacementBinders {α : Type} (tb : FVarId) (replacements : Array Vertex)
    (k : HashMap FVarId Expr → Array Expr → MetaM (Option α)) : MetaM (Option α) := do
  let oldDecl ← tb.getDecl
  let userName := oldDecl.userName
  let rec go (i : Nat) (remap : HashMap FVarId Expr) (newBinders : Array Expr) : MetaM (Option α) := do
    if h : i < replacements.size then
      let some newBinderType ← replaceBinderType? (← tb.getType) replacements[i] | return none
      withLocalDecl userName oldDecl.binderInfo newBinderType fun newBinder => do
        (go (i + 1) (if replacements.size == 1 then remap.insert tb newBinder else remap)
          (newBinders.push newBinder))
    else k remap newBinders
  go 0 {} #[]

/-- Helper to initialize the stale sets. -/
def staleSets (oldFV : FVarId) (post : Array Expr) : HashSet FVarId × HashSet FVarId :=
  let staleW := {oldFV}
  (staleW, post.foldl (init := staleW) (·.insert ·.fvarId!))

/--
Run continuation `k` on the `WeakenedDeclContext` resulting from replacing the `n`th targeted binder
of the declaration with type `type` with binders for `repls` and rebuilding all subsequent binders.
-/
def withWeakenedDecl {α : Type} (type : Expr) (n : Nat) (repls : Array Vertex)
    (k : WeakenedDeclContext →
    MetaM (Option α)) : MetaM (Option α) := do
  forallTelescope type fun args concl => do
    let some (ti, oldBinder) ← getNthTargetedBinder? args n | return none
    let oldFV := oldBinder.fvarId!
    let pre := args[0:ti].toArray
    let post := (args[ti+1:args.size]).toArray
    let (staleW, stale) := staleSets oldFV post
    withReplacementBinders oldFV repls fun remap₀ newBinders =>
      withoutLocalInstance oldFV do
        let rsCtx₀ : ReSynthContext := { remap := remap₀, stale, staleW }
        rsCtx₀.reSynthTelescope post.toList fun rsCtx rebuiltPost =>
          k { toReSynthContext := rsCtx, args, pre, newBinders, rebuiltPost, concl }


/--
Verify that, if we replace the `n`th targeted binder in `ciType` with binders for `repls`, the value
(usually a proof term) `val` can be re-synthesized in the weakened context. If so, returns `true`;
otherwise, returns `false`.

---
**Implementation notes**

`weakeningResynthesizable …` does not imply `(recompiledAgainst? …).isSome`, nor the other way
around: For example, the weakening candidate `[Group G] ↝ [MulOneClass G]` demonstrates three of the
possible cases through the three theorems below:

```
variable {G : Type} [inst : Group G] (a : G)
-- `weakeningResynthesizable` returns `true`, `(recompiledAgainst? …).isSome` returns `true`
theorem tt : a * 1 = a := mul_one a
-- `weakeningResynthesizable` returns `true`, `(recompiledAgainst? …).isSome` returns `false`
theorem tf : a * 1 = a := @mul_one G inst.toDivInvMonoid.toMonoid.toMulOneClass a
-- `weakeningResynthesizable` returns `false`, `(recompiledAgainst? …).isSome` returns `true`
theorem ft : a * 1 = a := by first | exact tt | exact mul_one a
```

The remaining case is demonstrated by the following example:

```
class A (α : Type) where
class B (α : Type) where n : Nat
instance A.toB {α : Type} [A α] : B α := ⟨42⟩

-- `weakeningResynthesizable` returns `false`, `(recompiledAgainst? …).isSome` returns `false`
theorem ff {α : Type} [A α] : B.n α = 42 := rfl
```

**Notes:**
* For theorem `ff`, the candidate wouldn't have been generated in the first place.
* We only actually call `weakeningResynthesizable` in the following two cases:
  * `redundancyGuard := true` (its default) and `reshapeRedundantToDrops` wants to verify whether
    dropping a seemingly redundant binder is safe.
  * `recompiledAgainst?` returned `none` and no candidate has been accepted yet (since
    `weakeningResynthesizable` replaces only one binder, and two binder weakenings individually
    being resynthesizable does not guarantee that they'd be resynthesizable jointly. In principle,
    nothing would prevent us from implementing a joint resynthesizability check, but we'd be adding
    complexity for very small gains).
-/
public def weakeningResynthesizable (ciType val : Expr) (n : Nat) (repls : Array Vertex) : MetaM Bool := do
  let holds? ← withWeakenedDecl ciType n repls fun ctx => do
    let body ← Core.betaReduce (mkAppN val ctx.args)
    let body' ← ctx.reSynthArg body
    let concl' ← ctx.reSynthExpr ctx.concl
    if mentions ctx.stale body' || mentions ctx.stale concl' then return false
    try
      if body'.hasExprMVar || body'.hasSorry then return false
      let concl' ← instantiateMVars concl'
      Meta.check concl'
      if concl'.hasExprMVar || concl'.hasSorry then return false
      let W ← instantiateMVars (← mkForallFVars ctx.weakenedTelescope concl')
      if W.hasLooseBVars || mentions ctx.stale W then return false
      Meta.check W
      Meta.check body'
      let bodyT' ← instantiateMVars (← inferType body')
      some <$> isDefEq bodyT' concl'
    catch _ => return false
  return holds?.getD false


/--
Given a statement with constant info `const`, returns the type of said statement after weakening,
for each `(n, repls)` in `ws`, the `n`th targeted binder of the statement with binders for `repls`.
-/
public def weakenedStatementType? (const : ConstantInfo) (ws : Array (Nat × Array Vertex)) : MetaM (Option Expr) := do
  let sorted := ws.qsort (fun a b => a.1 > b.1)
  let mut type := const.type
  for (k, repls) in sorted do
    let some t ← rebuiltStatementType type k repls | return none
    type := t
  return some type
where
  rebuiltStatementType (type : Expr) (n : Nat) (repls : Array Vertex) : MetaM (Option Expr) := do
    withWeakenedDecl type n repls fun ctx => do
      let concl' ← ctx.reSynthExpr ctx.concl
      if mentions ctx.stale concl' then return none
      let type ← instantiateMVars (← mkForallFVars ctx.weakenedTelescope concl')
      if type.hasLooseBVars || type.hasExprMVar || mentions ctx.stale type then return none
      unless ← isTypeCorrect type do return none
      return some type
