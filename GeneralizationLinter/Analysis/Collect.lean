/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
module

import Lean.Util.CollectLevelParams
import Lean.Meta.Transform

public import GeneralizationLinter.Graph.Canonicalization
import GeneralizationLinter.Graph.ClassGraph
import GeneralizationLinter.Analysis.Options

open Lean Meta
open Std (HashMap)

namespace GeneralizationLinter
open Digraph Digraph.Condensation

/-!
# Collect

## Preliminaries

We use the term "instance transformers" (or simply "transformers") to refer to instances which map
one or more instances to another instance. For example, `CommGroup.toGroup` is an instance
transformer. An "instance transformation" (or simply "transformation"), meanwhile, will refer to an
application of an instance transformer, e.g. `@CommGroup.toGroup G inst`. Note that both instance
transformers and instance transformations are themselves instances; the former are declared as such,
while the latter are instance-valued expressions. To disambiguate, we will refer to instances that
aren't instance transformers or instance transformations as "root instances".

Oftentimes, transformations may be nested:

```
Weak.toWeakest α (Strong.toWeak α (Strongest.toStrong α ⟨inst of Strongest on α⟩))
                                                        └──────── root ────────┘
```

These nested transformations often involve "junctions": transformations that have ≥2 class-typed
args. Sometimes, these junctions are bona-fide **_confluences_**, as is the case for e.g.
`Prod.instMonoid {M : Type u} {N : Type v} [Monoid M] [Monoid N] : Monoid (M × N)`, where the
conclusion isn't just a "projection" of one of the class-typed args. In many other cases, the
junctions _are_ such projections, however (if not technically then at least in spirit). We call
junctions of this second kind **_tributary junctions_**, borrowing from hydrology again, and
distinguish two sub-categories:

* **Unconditional tributary junctions (UTJ)** (projections): When one (and only one) of the
  class-typed args contains all other args in its type, then that single class-typed arg "pins" (or
  "fixes") the values of all other arguments (no matter their annotation) through unification, i.e.,
  it's the sole degree of freedom. As such, when we have, for example, an instance of
  `IsStrictOrderedRing R` — or, written more explicitly, an instance `inst₃ :
  @IsStrictOrderedRing.{u} R inst₁ inst₂`, where `inst₁ : Semiring.{u} R` and `inst₂ :
  PartialOrder.{u} R` — then that instance alone, through its type, pins all the other arguments
  (including universe levels) of, for example, the transformation
  `IsStrictOrderedRing.toIsOrderedRing`:

  ```
  instance IsStrictOrderedRing.toIsOrderedRing.{u} {R : Type u}
    [Semiring R]               -- [inst₁ : Semiring.{u} R]
    [PartialOrder R]           -- [inst₂ : PartialOrder.{u} R]
    [IsStrictOrderedRing R] :  -- [inst₃ : @IsStrictOrderedRing.{u} R inst₁ inst₂],
    IsOrderedRing R            -- @IsOrderedRing.{u} R inst₁ inst₂
  ```

  Hence, we treat `IsStrictOrderedRing.toIsOrderedRing` as a mere projection of `IsStrictOrderedRing
  R`: hand someone `inst₃`, and they can take `IsStrictOrderedRing.toIsOrderedRing`, fill out all
  other argument slots, and give you an instance of `IsOrderedRing R`.

  We call `inst₃` the "source" of the transformation (it's what the projection is "forgetting
  from"). We call class-typed arguments other than the source "tributaries".

  * **NB:** In auto-generated projections (`IsStrictOrderedRing.toIsOrderedRing` is not one),
    `inst₃` would be called `self`. See e.g. `IsStrictOrderedRing.toPosMulStrictMono`.

* **Conditional tributary junctions (CTJ):** When we add one or more `Prop` mixins to what would
  otherwise have been an unconditional tributary junction, we get a conditional tributary junction.
  Here, we have that, under the assumption that the mixins are satisfied, this junction is also
  essentially a projection in spirit. Nonetheless, CTJ's are out of scope for now. Examples of CTJ's
  include `LeftCancelMonoid.groupOfFinite`

  * CTJs would need tie-breakers. For example:

    ```
    IsNoetherianRing.wfDvdMonoid.{u} : forall {R : Type.{u}}
      [inst₁ : CommSemiring.{u} R]
      [inst₂ : IsDomain.{u} R (CommSemiring.toSemiring.{u} R inst₁)]
      [h : IsNoetherianRing.{u} R (CommSemiring.toSemiring.{u} R inst₁)],
      WfDvdMonoid.{u} R (CommSemiring.toCommMonoidWithZero.{u} R inst₁)
    ```

    here, if we removed either the `IsDomain R` or `IsNoetherianRing R` mixins, we'd have a UTJ (as
    well as an impossible-to-prove signature, but that's beside the point) with `h` or `inst₂` as
    sources, respectively. However, the signature per se doesn't tell us whether we should treat
    `IsDomain R` as the mixin or `IsNoetherianRing R`. One sensible heuristic would be to check the
    class names of the types against the namespace of the transformation, which in this case would
    pick `h` as the source and designate `inst₂` as the mixin.

  * CTJs can be tricky to detect reliably. Take the following non-example:

    ```
    LeftCancelMonoid.groupOfFinite.{u} : forall {G : Type.{u}}
      [inst₁ : LeftCancelMonoid.{u} G]
      [inst₂ : Finite.{succ u} G],
      Group.{u} G
    ```

    Here, if we adopted the namespace tie-breaker we suggested before, `inst₁` would be chosen as
    the source, and `inst₂` would be chosen as the mixin. But to call
    `LeftCancelMonoid.groupOfFinite` a projection from `LeftCancelMonoid G` to `Group G` conditioned
    on `Finite G` would flow in the opposite direction of strength, as `Group G` is strictly
    stronger than `LeftCancelMonoid G` (if `inst : Group G`, then `@CancelMonoid.toLeftCancelMonoid
    G (@Group.toCancelMonoid G inst)` yields an instance of `LeftCancelMonoid G`).

    Whether this would inherently be a problem further down the road is hard to say, but it
    contradicts our intent and hence motivates us to shelf this feature for now.

## This module

This module concerns itself with finding out what classes a declaration actually uses each of its
targeted binders as (which we'll use to set the requirements that any weakening of that binder must
still satisfy).

> We use the following artificial declaration and proof as a guiding example:
>
> ```
> theorem thm {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (r : R) (m : M) :
>     r • (m + m) = r • m + r • m := smul_add r m m
> ```
>
> Now, let `sig` be the `Expr` corresponding to `{R M : Type*} [Ring R] [AddCommGroup M] [Module R
> M] (r : R) (m : M) : r • (m + m) = r • m + r • m`, and let `proof` be the `Expr` corresponding to
> `smul_add r m m`.

For a given pair `sig proof : Expr`, where `proof` is the proof of `sig`, we begin by calling
`getTargetedBinders sig`, which will assign each targeted (class) binder of `sig` an fvar, which
we'll treat as the targeted binder's "canonical" fvar. To encode this "canonicity", we create the
wrapper type `BinderId` around `FVarId`. These fvars are returned within an array of
`TargetedBinder`s, each containing a `BinderId`. The array obeys the order in which the targeted
binders appear in `sig`. Call that array `tbinders`.

> In our example, `tbinders = #[inst₁, inst₂, inst₃]`, where `inst₁` is the "canonical" fvar of the
> `Ring R` instance, `inst₂` that of the `AddCommGroup M` instance, and `inst₃` that of the `Module
> R M` instance.

Next, we call `getMIChains tbinders sig proof`. Now, `getMIChains` will telescope `sig` once more,
generating fresh fvars for all binders. However, given that it's the same `sig` as was passed to
`getTargetedBinders`, we can define a bijection between the targeted binder fvars from
`getTargetedBinders` and the corresponding fvars generated by the telescope in `getMIChains` by
using the fvars' positional indices within `sig`. We store this bijection as `binderIdOf`.

> In our example, say that `getMIChains`'s `forallTelescope sig` produces the binder fvars `R' M'
> inst₁' inst₂' inst₃' r' m'`. Then `binderIdOf` is the bijection `{inst₁' ↦ inst₁, inst₂' ↦ inst₂,
> inst₃' ↦ inst₃}` from `getMIChains`'s targeted binder fvars `inst₁' inst₂' inst₃'` to their
> matching `BinderId`s.

After this bijection is established, `getMIChains` then `walk`s

* every binder's type,
* the `sig`'s conclusion, and
* the proof term "syntactically applied" to `getMIChains`'s telescope and β-reduced (the β-reduction
  is what transforms the syntactic application `@proof R' M' inst₁' inst₂' inst₃' r' m'` into an
  `Expr` of `proof` where all its binder bvars are replaced with the corresponding fvars from
  `getMIChains`'s telescope).

*Note:* An targeted binder only appearing within another targeted binder's type, and nowhere else,
does not mean that it is superfluous.

> In our example, the things `getMIChains` will walk look like this:
> * "every binder's type": `Type*`, `Type*`, `Ring R'`, `AddCommGroup M'`, `@_root_.Module R' M'
>   (@Ring.toSemiring R' inst₁') (@AddCommGroup.toAddCommMonoid M' inst₂')`, `R`, and `M`.
> * "the `sig`'s conclusion": `@Eq M' (...) (...)` (very long, with plenty of instance chains).
> * "the proof term applied to `getMIChains`'s telescope and β-reduced":
>   ```
>   @smul_add R' M'
>   (@AddMonoid.toAddZeroClass M'
>     (@SubNegMonoid.toAddMonoid M' (@AddGroup.toSubNegMonoid M' (@AddCommGroup.toAddGroup M' inst₂'))))
>   (@DistribMulAction.toDistribSMul R' M' (@Semiring.toMonoid R' (@Ring.toSemiring R' inst₁'))
>     (@SubNegMonoid.toAddMonoid M' (@AddGroup.toSubNegMonoid M' (@AddCommGroup.toAddGroup M' inst₂')))
>     (@Module.toDistribMulAction R' M' (@Ring.toSemiring R' inst₁') (@AddCommGroup.toAddCommMonoid M' inst₂') inst₃'))
>   r' m' m'
>   ```

`walk` is defined inductively over every possible `Expr` constructor. Its job is to find any spot
where the elaborator put an instance transformation or root instance. It recurses through function
applications, projections, `let`s, and `fun` and `∀` abstractions. In the case of `fun` and `∀`
abstractions, it walks the domain type first, and then the body, with the abstracted bvar within it
instantiated to a fresh fvar of the right type, since `walk` can't query the type of anything that
contains a loose bvar.

As it recurses, there are exactly two spots at which `walk` will pass a subterm to `route`:

1. The subterm is an argument in an application.
2. The subterm is the base of a projection (`.proj`).

Once `walk` passes a subterm `e` to `route`, `route` decides what to do next based on the type of
the subterm. If it's class-typed, it runs `collect e none`, starting a new chain. If it's not
class-typed, `route` hands `e` back to `walk` to keep recursing on.

Assuming that the subterm is an instance chain, `collect` will record what class the chain is an
instance of (i.e., the head of the subterm's outermost class application) and carry it with it as
`chainHead?` as it descends the chain. At every instance transformation (e.g.
`Module.toDistribMulAction ...`), `collect` will call `walk` on all non-class-typed arguments to
ensure any instances that might have been involved in the construction of the non-class-typed
argument are still taken into account. With regards to class-typed arguments, we differentiate
between two main cases:

* **Only 1 class-typed argument:** `collect` continues the current chain by descending into the
  class-typed argument.

* **≥2 class-typed arguments (junction):** `collect` tries to figure out what kind of junction this
  is by calling `sourceArg?`:

  * `sourceArg?` returns `some ...`: `collect` continues the current chain by descending into the
    source argument, and starts new chains at every other class-typed argument. This happens when
    the junction is an unconditional tributary junction.

  * `sourceArg?` returns `none`: `collect` drops the current chain and starts new chains at each
    class-typed argument. This happens when the junction is a confluence, and currently also when it
    is a conditional tributary junction.

Once the `MIChain`s have been collected, `getMIChains` returns them. We then pass the chains to
`getReqs`, which associates each chain to the corresponding `TargetedBinder`. It then converts each
chain to a `Requirement`, and returns the requirements as an array.

> In our example, the collected `MIChains` are
>
> * `{ head := Monoid R', inst := inst₁' }` (4 times)
> * `{ head := Semiring R', inst := inst₁' }` (5 times)
> * `{ head := Add M', inst := inst₂' }` (2 times)
> * `{ head := AddCommMonoid M', inst := inst₂' }` (5 times)
> * `{ head := AddMonoid M', inst := inst₂' }` (4 times)
> * `{ head := AddZeroClass M', inst := inst₂' }` (4 times)
> * `{ head := Zero M', inst := inst₂' }` (3 times)
> * `{ head := DistribSMul R' M', inst := inst₃' }` (1 time)
> * `{ head := SMul R' M', inst := inst₃' }` (3 times)
-/

/--
Structure to help differentiate between the `FVarId` assigned to a binder by the telescope inside
`getTargetedBinders` and any other `FVarId`s that other telescopes (specifically, that of `getMIChains`)
may assign to the same binder.
-/
public structure BinderId where
  /-- The `FVarId` assigned to the binder by the telescope inside `getTargetedBinders`. -/
  fvar : FVarId
deriving BEq, Hashable, Inhabited


/-- Targeted binder in a declaration. -/
public structure TargetedBinder extends Key where
  /-- fvar ID generated for this binder when `getTargetedBinders` telescopes the declaration. -/
  fvar : BinderId
  /--
  Binder's 0-indexed position among the declaration's targeted binders. This allows
  `ReSynth.rebuildWeakened` to locate the binder despite re-telescoping the declaration with fresh
  fvars.
  -/
  idx : Nat
  /-- Binder's annotation. -/
  binderInfo : BinderInfo
deriving Inhabited


/-- Get `Name` of class head of a `TargetedBinder`'s type. -/
public def TargetedBinder.origName (b : TargetedBinder) : Name := b.toVertex.name


/--
Maximal instance chain.

---
**Example**

Suppose we have `[inst : Group α]` and a maximal instance chain `@DivInvMonoid.toMonoid α
(@Group.toDivInvMonoid α inst)`. Then the corresponding `MIChain` record for this chain would be:

```
{
  inst := ⟨`_uniq.123⟩, -- TargetedBinder.fvar of `inst`
  head := {
    name := `Monoid,
    pattern := #[.bvar 0],
    levels := .polymorphic, -- or `.concrete #[…]`
    subst := #[.fvar ⟨`_uniq.124⟩] -- array containing fvar `α`
  }
}
```
-/
public structure MIChain where
  /-- The "resulting" class application of the chain. -/
  head : Key
  /-- The `TargetedBinder.fvar` corresponding to the instance at the root of the chain. -/
  inst : BinderId
deriving Inhabited


/--
A minimal requirement that a proof or statement imposes on a specific targeted binder of the
statement.

---
**Implementation notes**

* For any given declaration, there's a simple bijection between the `MIChain`s and `Requirement`s
  associated with the declaration, and the two structures contain essentially the same data. The
  structures are kept separate to aid modularity and future extensibility of the
  binders-and-requirements collection pipeline.
* The fact that each `Requirement` is associated with a specific `TargetedBinder` is technically an
  unnecessary restriction on the kinds of weakenings the linter can suggest, but it simplifies the
  search for weakenings from general abduction to computing some least upper bounds, and we find
  that it doesn't reduce the quality of the suggestions too much.

---
**Example**

Suppose we have a theorem `theorem thm {α} [inst : Group α] ... : ... := ...`. Suppose that `b :
TargetedBinder` corresponds to the instance-implicit binder `[Group α]`, and that the proof term of
`thm` includes the maximal instance chain `@DivInvMonoid.toMonoid α (@Group.toDivInvMonoid α inst)`.
Then the corresponding `Requirement` record for this chain would be:

```
{
  binder := { … }, -- b.fvar
  name := `Monoid,
  pattern := #[.bvar 0],
  levels := .polymorphic, -- or `.concrete #[…]`
  subst := #[.fvar ⟨`_uniq.124⟩] -- array containing fvar `α`
}
```

Intuitively, this `Requirement` record is expressing that the instance-implicit binder `b` must be
able to provide an instance of `Mul α`.
-/
public structure Requirement extends Key where
  binder : TargetedBinder
deriving Inhabited


/--
Returns `true` if the local declaration is an instance-implicit class binder, and `false` otherwise.

---
**Implementation notes**

Instance-implicit binders are almost always classes, and this is enforced by the default-on
`checkBinderAnnotations`, but they're not technically required to be (see e.g.
`Mathlib.CategoryTheory.Bundled.of`), so we check out of an abundance of caution.
-/
public def isTargetedBinder (ld : LocalDecl) : MetaM Bool := do
  unless (← isClass? ld.type).isSome do return false
  match ld.binderInfo with
  | .instImplicit => return true
  | .implicit | .strictImplicit =>
    return (← getOptions).getBool ``generalizeTypeclasses.targetImplicit (defVal := true)
  | .default => return false


/--
Given `type` of the form `forall xs, A`, extract the targeted binders of `xs` as local declarations
`lds` and run `k lds A`.

---
**Example**

`targetedBinderTelescope "{R} [CommRing R] {K} [Field K] → C" k` will run `k #["CommRing R", "Field
K"] "C"`, where `"{R} [CommRing R] {K} [Field K] → C"` and `"C"` are to be understood as `Expr`s and
`"CommRing R"` and `"Field K"` as `LocalDecl`s.
-/
public def targetedBinderTelescope {α : Type} (type : Expr) (k : Array LocalDecl → Expr → MetaM α) :
    MetaM α :=
  forallTelescope type fun xs concl => do
    let mut lds : Array LocalDecl := #[]
    for x in xs do
      let ld ← x.fvarId!.getDecl
      if ← isTargetedBinder ld then lds := lds.push ld
    k lds concl


/-- Get the targeted binders of a declaration. -/
public def getTargetedBinders (decl : Expr) : MetaM (Array TargetedBinder) := do
  forallTelescope decl fun xs _ => do
    let mut binders : Array TargetedBinder := #[]
    for x in xs do
      let ld ← x.fvarId!.getDecl
      if ← isTargetedBinder ld then
        let app ← toKey (← whnf ld.type)
        binders := binders.push {
          toKey := app,
          fvar := ⟨x.fvarId!⟩,
          idx := binders.size
          binderInfo := ld.binderInfo
        }
    return binders

initialize declSourceCacheRef : IO.Ref (HashMap Name (Option Nat)) ← IO.mkRef {}

/--
Get index of source slot for a given declaration. Doing this once for each declaration and memoizing
the result makes descent through instance chains a lot faster.
-/
public def declSource? (fn : Name) : MetaM (Option Nat) := do
  if let some memo := (← declSourceCacheRef.get)[fn]? then return memo
  let some info := (← getEnv).find? fn | return none
  let verdict ← forallTelescopeReducing info.type fun args concl => do
    -- If conclusion isn't class-typed, then `fn` isn't even a transformation. Example: `map_one`
    unless (← isClass? concl).isSome do return none
    -- If there are no arguments, then `fn` isn't a transformation either. Example: `instAddNat :
    -- Add ℕ`.
    if args.isEmpty then return none
    -- If there is a source, then it has to be the last binder, since any other binder's type
    -- wouldn't be able to contain every other binder, since binder types can't contain binders that
    -- haven't been introduced yet.
    let i := args.size - 1
    let srcT ← inferType args[i]!
    for j in [0:i] do
      unless srcT.containsFVar args[j]!.fvarId! do return none
    let srcLevels := (collectLevelParams {} srcT).params
    let unpinned := (collectLevelParams {} concl).params.filter (!srcLevels.contains ·)
    if unpinned.isEmpty then return some i
    let mut others : CollectLevelParams.State := {}
    for j in [0:i] do
      others := collectLevelParams others (← inferType args[j]!)
    return if unpinned.any others.params.contains then none else some i
  declSourceCacheRef.modify (·.insert fn verdict)
  return verdict


/--
Given the instance arguments `inst₁ … instₙ` of an application, check if there's a _unique_ `i` such
that `instᵢ`'s type contains `instⱼ` for all `j ∈ {1, …, n}`. If there is, return `some instᵢ`.
Otherwise, return `none`.

This is used to handle junctions of instance chains effectively. For example, if we have
`@DistribMulAction.toDistribSMul M A inst_Monoid_M inst_AddMonoid_A inst_DistribMulAction_M_A`, then
the source is `inst_DistribMulAction_M_A`, as its type `@DistribMulAction M A inst_Monoid_M
inst_AddMonoid_A` contains all the other arguments.
-/
def sourceArg? (e : Expr) : MetaM (Option Expr) := do
  let e := e.consumeMData
  let args := e.getAppArgs
  if let some f := e.getAppFn.constName? then
    -- const-headed: consult `declSource?`
    let some i ← declSource? f | return none
    return args[i]?
  -- fvar-headed: candidates are args (not necessarily the last arg) that contain every other arg
  let cands ← args.filterM fun arg => do
    let argT ← inferType arg
    args.allM fun a => return a == arg || (argT.find? (· == a)).isSome
  return if cands.size == 1 then cands[0]? else none


/-- State monad to keep track of the `MIChain`s we've collected. -/
private abbrev CollectM := StateRefT (Array MIChain) MetaM


/--
Does the constant `name` have any `outParam` or `semiOutParam` parameter?

---
**Examples**

```
let env ← getEnv
-- class Monoid (M : Type u) : Type u
hasDispatchSlot env `Monoid = false
-- class MulHomClass (F : Type u) (M : outParam (Type v)) (N : outParam (Type w))
--   [Mul M] [Mul N] [FunLike F M N] : Prop
hasDispatchSlot env `MulHomClass = true
-- class SetLike (A : Type u) (B : outParam (Type v)) : Type (max u v)
hasDispatchSlot env `SetLike = true
-- class Coe (α : semiOutParam (Sort u)) (β : Sort v) : Sort (max (max 1 u) v)
hasDispatchSlot env `Coe = true
-- class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) : Type (max (max u v) w)
hasDispatchSlot env `HMul = true
-- class DFunLike (F : Sort u) (α : outParam (Sort v)) (β : outParam (α → Sort w)) :
--   Sort (max (max (max 1 u) v) w)
hasDispatchSlot env `DFunLike = true
-- abbrev FunLike (F : Sort u) (α : Sort v) (β : Sort w) : Sort (max (max (max 1 u) v) w)
hasDispatchSlot env `FunLike = false -- even though `FunLike` is an abbrev of `DFunLike`
```

**Note:** The case of `FunLike` is not important for us, because `FunLike` would get reduced to
`DFunLike` before `hasDispatchSlot` would ever be called on it.
-/
private def hasDispatchSlot (env : Environment) (name : Name) : Bool :=
  match env.find? name with
  | some info => go info.type
  | none => false
where
  go : Expr → Bool
    | .forallE _ bt b _ =>
      bt.consumeMData.isAppOfArity ``outParam 1 ||
      bt.consumeMData.isAppOfArity ``semiOutParam 1 ||
      go b
    | _ => false


/--
Returns `some head` if `head` should be propagated through a descent step, or `none` if it
shouldn't. If it shouldn't, that means `collect` will drop the chain and start a new one.

---
**Implementation notes**

`propagatedHead?` returns `none` iff
1.  the transformation `linkT` contains arguments that are not "statable" using the source's
    arguments, or
2.  the `head` has more open arguments than the source and has an `outParam` or `semiOutParam`.

Condition 1 is inherited from condition 1 of `isWeakeningEdge`.
Condition 2 is a heuristic that aims to reduce non-idiomatic suggestions like `Mul α ↝ HMul α α α`
or `Preorder α ↝ Trans LT.lt LT.lt LT.lt`.

**Note:** Condition 2 of `isWeakeningEdge` is encoded separately in `sourceArg?`.

---
**Examples**

Examples where `propagatedHead?` returns `some head`:

* `CommMonoid M ↝ Monoid M`
* `Mul R ↝ SMul R R`
* `IsSimpleModule R M ↝ Nontrivial (Sub' R M)`
* `Algebra R A ↝ IsScalarTower R A A`
* `MonoidHomClass F M N ↝ MulHomClass F M N`

Examples where `propagatedHead?` returns `none`:

* `IsCoatomic α ↝ IsAtomic αᵒᵈ` (condition 1)
* `Monad m ↝ ForIn m ρ α` (conditions 1 and 2, though condition 1 short-circuits already)
* `Mul α ↝ HMul α α α` (condition 2)
* `Preorder α ↝ Trans LT.lt LT.lt LT.lt` (condition 2)
-/
def propagatedHead? (head : Key) (linkT : Expr) (src : Expr) : MetaM (Option Key) := do
  let srcT ← whnf (← inferType src)
  let srcArgs := srcT.getAppArgs
  -- The transformation's open frame args that are not syntactically equal to one of `src`'s args.
  let rough := (← frameArgs linkT).filter (fun c => !srcArgs.contains c)
  -- If all of the transformation's open frame args are syntactically equal to one of `src`'s args,
  -- we know for sure that condition 1 is satisfied. If not, we need to check more carefully.
  unless rough.isEmpty do
    let srcSubjects ← frameArgs srcT
    let isClosed (e : Expr) : MetaM Bool := pure (!e.hasFVar && !srcSubjects.any (·.occurs e))
    unless ← rough.allM (statableFrom srcArgs isClosed) do
      return none
  -- If `head` has more open key args than the source _and_ has an `outParam` or `semiOutParam`, we
  -- drop the chain. That's mostly because we don't want to be suggesting weakenings like `[Mul α] ↝
  -- [HMul α α α]`.
  let srcKey ← toKey srcT
  let openArity (k : Key) : Nat := k.pattern.countP (·.hasLooseBVars)
  if openArity head ≤ openArity srcKey then return some head
  return if hasDispatchSlot (← getEnv) head.name then none else some head


/--
If `e` is an application of a dynamically generated constant (e.g., `_proof_*`, `T.match_1`, etc.)
and which has some targeted binder's fvar as one of its direct arguments, we unfold `e` and return
its body β-reduced against `e`'s arguments. This allows us to avoid having `e`'s signature introduce
needlessly strong requirements, which dynamically generated constants tend to do.
-/
private def unfoldInternalHead? (binderIdOf : HashMap FVarId BinderId) (e : Expr) :
    MetaM (Option Expr) := do
  let .const declName levels := e.getAppFn | return none
  unless declName.isInternalDetail do return none
  let args := e.getAppArgs
  unless args.any (fun arg => arg.isFVar && binderIdOf.contains arg.fvarId!) do return none
  let some info := (← getEnv).find? declName | return none
  let some val := info.value? (allowOpaque := true) | return none
  return some ((val.instantiateLevelParams info.levelParams levels).beta args)

mutual


/--
Decide what to do with `e`:
* If `e` is a class application `C a₁ … aₙ`, then call `collect` on `e`, starting a new chain with
  `C` (converted to a `Key`) as `head`.
* If `e` is not a class application, call `walk` on `e`.
-/
private partial def route (binderIdOf : HashMap FVarId BinderId) (e : Expr) :
    CollectM Unit := do
  if (← isClass? (← inferType e)).isSome then collect binderIdOf e none
  else walk binderIdOf e


/--
If `e` corresponds to a maximal instance chain, `collect` will record that instance chain as an
`MIChain`. If `e` does not correspond to a maximal instance chain, then `collect` will recursively
find any maximal instance chains that it may contain.
-/
private partial def collect (binderIdOf : HashMap FVarId BinderId) (e : Expr)
    (chainHead? : Option Key) : CollectM Unit := do
  let e := e.consumeMData -- strip .mdata
  -- See `unfoldInternalHead?`.
  if let some e' ← unfoldInternalHead? binderIdOf e then
    collect binderIdOf e' chainHead?
    return
  -- Pi-instance (e.g. `Pi.instMul`)
  if let .lam binderName binderType body binderInfo := e then
    withLocalDecl binderName binderInfo binderType fun x =>
      collect binderIdOf (body.instantiate1 x) chainHead?
    return
  let fn := e.getAppFn
  let args := e.getAppArgs
  -- If application head is one of the targeted binders: we found an `MIChain`.
  if let .fvar fvarId := fn then
    if let some root := binderIdOf.get? fvarId then
      let app ← chainHead?.getDM do toKey (← whnf (← inferType e))
      modify (·.push { head := app, inst := root }) -- record `MIChain`
      for arg in args do route binderIdOf arg -- args may contain more chains still
      return
  -- Not an application ⟹ no arguments to route through. Call `walk` instead.
  unless e.isApp do
    walk binderIdOf e
    return
  let linkT ← whnf (← inferType e)
  -- If not class-typed, pass to `walk`
  unless (← isClass? linkT).isSome do
    walk binderIdOf e
    return
  -- `e` is a class-typed application, e.g. `@Group.toDivInvMonoid α inst`
  let head ← chainHead?.getDM (toKey linkT)
  match ← sourceArg? e with
  | some src =>
    -- descend into source
    collect binderIdOf src (← propagatedHead? head linkT src)
    -- check out non-source args too
    for arg in args do
      unless arg == src do route binderIdOf arg
  | none =>
    -- confluence: start new chain for each arg
    for arg in args do route binderIdOf arg


/-- Find any spot in `e` where the elaborator put an instance transformation or root instance. -/
private partial def walk (binderIdOf : HashMap FVarId BinderId) (e : Expr) :
    CollectM Unit := do
  match e with
  | .app .. =>
    -- See `unfoldInternalHead?`.
    if let some e' ← unfoldInternalHead? binderIdOf e then
      walk binderIdOf e'
    else e.withApp fun fn args => do
      for arg in args do route binderIdOf arg
      walk binderIdOf fn -- the application head itself may also contain chains, so `walk` it
  | .proj _ _ struct => route binderIdOf struct -- collect on `struct` directly
  | .lam binderName binderType body binderInfo
  | .forallE binderName binderType body binderInfo =>
    walk binderIdOf binderType
    -- instantiate the loose bvar in `body`, since otherwise `inferType` fails in `route`
    withLocalDecl binderName binderInfo binderType fun x => walk binderIdOf (body.instantiate1 x)
  | .letE declName type value body _ =>
    walk binderIdOf type
    walk binderIdOf value
    withLetDecl declName type value fun x => walk binderIdOf (body.instantiate1 x)
  | .mdata _ expr => walk binderIdOf expr
  | .const .. | .fvar .. | .bvar .. | .sort .. | .mvar .. | .lit .. => pure ()

end


/-- Collect all `MIChain`s from `decl` and `proof`. -/
public def getMIChains (binders : Array TargetedBinder) (decl proof : Expr) :
    MetaM (Array MIChain) := do
  forallTelescope decl fun xs concl => do
    let mut binderIdOf : HashMap FVarId BinderId := {}
    let mut k := 0
    for x in xs do
      let ld ← x.fvarId!.getDecl
      if ← isTargetedBinder ld then
        if let some b := binders[k]? then
          binderIdOf := binderIdOf.insert x.fvarId! b.fvar
        k := k + 1
    let go : CollectM Unit := do
      for x in xs do walk binderIdOf (← x.fvarId!.getType)
      walk binderIdOf concl
      walk binderIdOf (← Core.betaReduce (mkAppN proof xs))
    let (_, chains) ← go.run #[]
    return chains


/--
Convert an array of `MIChain`s into an array of `Requirement`s, filtering out `MIChain`s that aren't
rooted at one of the targeted binders.
-/
public def getReqs (binders : Array TargetedBinder) (chains : Array MIChain) :
    MetaM (Array Requirement) := do
  let binderOfId : HashMap BinderId TargetedBinder :=
    binders.foldl (init := {}) fun binderOfId' b => binderOfId'.insert b.fvar b
  return chains.filterMap fun c =>
    match binderOfId[c.inst]? with
    | some b => some { toKey := c.head, binder := b }
    | none => none
