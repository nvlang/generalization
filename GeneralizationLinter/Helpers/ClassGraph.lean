/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
module

public import Lean.Expr
public import Lean.Environment
public import Lean.Meta
public import GeneralizationLinter.Helpers.Digraph
public import GeneralizationLinter.Helpers.Vertex
public import GeneralizationLinter.Helpers.Canonicalization

open Lean Meta

namespace GeneralizationLinter
open Digraph

open Std (HashSet)

/-!
# Class Graph

Builds the class graph from the environment.

---
**Main definitions**

* `isWeakeningEdge`: helper for `extractEdge?` that determines whether an edge should be considered
  a weakening edge.
* `extractEdge?`: convert an instance into a `ClassEdge`, if appropriate.
* `ofEnv`: build the class graph from the environment.

---
**References**

* [A. J. Best. 2023. _Automatically Generalizing Theorems Using
  Typeclasses_.][best2023automaticallyGeneralizingTheorems]
-/



/-! ## Edges -/

/-- An edge of the class graph. -/
public structure ClassEdge where
  /-- Source vertex of the edge. This is the _stronger_ class, the one we're weakening _from_. -/
  src : Vertex
  /-- Target vertex of the edge. This is the _weaker_ class, the one we're weakening _to_. -/
  tgt : Vertex

/-! ## Extraction -/

/--
Returns an array of the `Sort`-typed arguments of a class application, i.e., its
_carriers_, as opposed to its data arguments.

---
**Examples**

```
-- class IsPreorder (α : Sort*) (r : α → α → Prop) : Prop
carrierArgs (@IsPreorder α r) = #[α]
-- class CharP (R : Type*) [AddMonoidWithOne R] (p : outParam ℕ) : Prop
carrierArgs (@CharP R _ p) = #[R]
-- class Module (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] : Type (max u v)
carrierArgs (@Module R M _ _) = #[R, M]
```
-/
public def carrierArgs (classAppE : Expr) : MetaM (Array Expr) :=
  classAppE.getAppArgs.filterM fun a => return (← inferType a).isSort

/--
The non-instance-implicit arguments of a class application. These are the arguments that are used by
`reifyClass` to reify a suggestion candidate. We call these arguments the ***frame arguments*** or
***frame*** of a class application.

There can be some overlap between frame arguments and targeted binders, which is fine, because we're
not using frame arguments to index entries of the class graph, but rather just to reify suggestion
candidates.

---
**Examples**

```
-- class IsPreorder (α : Sort*) (r : α → α → Prop) : Prop
frameArgs (@IsPreorder α r) = #[α, r]
-- class CharP (R : Type*) [AddMonoidWithOne R] (p : outParam ℕ) : Prop
frameArgs (@CharP R _ p) = #[R, p]
-- class Module (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] : Type (max u v)
frameArgs (@Module R M _ _) = #[R, M]
```
-/
public def frameArgs (classAppE : Expr) : MetaM (Array Expr) := do
  let paramInfos := (← getFunInfo classAppE.getAppFn).paramInfo
  return classAppE.getAppArgs.zipIdx.filterMap fun (arg, i) =>
    if (paramInfos[i]?.map (·.binderInfo.isInstImplicit)).getD false then none else some arg

/--
Helper for `extractEdge?` which, given some information about the instance declaration that
`extractEdge?` is processing, indicates whether the edge is a weakening edge, which is the case iff
all of the following conditions are satisfied:


1.  Target has ≥1 carriers.

    * Why? TODO

2.  Target's frame args are subset of source's frame args (up to definitional equality).

    * Why? TODO

3.  Every class-typed argument of the declaration other than the source must be contained
    in the source's type.

    * Why? TODO

---
**Examples**

```
-- instance IsPreorder.toIsTrans {α r} [IsPreorder α r] : IsTrans α r
isWeakeningEdge (IsPreorder α r) (IsTrans α r) #[] = true

-- instance Module.toDistribMulAction {R M} [Semiring R] [AddCommMonoid M]
--   [Module R M] : DistribMulAction R M
isWeakeningEdge (Module R M) (DistribMulAction R M) #[Semiring R, AddCommMonoid M] = true

-- instance asymm_of_isTrans_of_irrefl [IsTrans α r] [Std.Irrefl r] : Std.Asymm r
isWeakeningEdge (Std.Irrefl r) (Std.Asymm r) #[IsTrans α r] = false -- source doesn't contain
                                                                    -- IsTrans α r

-- instance Prod.instMonoid [Monoid M] [Monoid N] : Monoid (M × N)
isWeakeningEdge (Monoid N) (Monoid (M × N)) #[Monoid M] = false -- different carrier

-- artificial examples
isWeakeningEdge (IsEmpty α) (IsWellOrder α r) #[] = false -- fresh `r`
isWeakeningEdge (Std.Irrefl r) (Std.Refl rᶜ) #[] = false -- transformed relation
```
-/
public def isWeakeningEdge (s t : Expr) (otherPrems : Array Expr) :
    MetaM Bool := do
  -- Condition 1: If target class app has no carriers, reject (e.g., Nat.AtLeastTwo n)
  if (← carrierArgs t).isEmpty then return false
  -- Condition 2: All of target's non-inst args must be defeq to some arg of source
  let sArgs := s.getAppArgs
  let tArgs ← frameArgs t
  let weakening ← tArgs.allM fun tArg => sArgs.anyM fun sArg => isDefEq tArg sArg
  unless weakening do return false -- if not a weakening, reject
  -- every class-typed arg of declaration (other than `s`) must be contained in `s`'s type
  let allSrcArgs := s.getAppArgs
  return otherPrems.all fun p => allSrcArgs.contains p

/--
Usually, canonicalized arguments are plain bvars. However, sometimes they may actually "structured",
i.e., an application.

If $n≥1$ canonicalized arguments are applications, this function returns the $n$ heads of those
applications (one per structured canonicalized argument, always the head of the outer-most
application). Otherwise it returns the empty set.

---
**Examples**

```
ContinuousAlgEquivClass α β γ δ       → {}
Small (Subtype α)                     → {Subtype}
HasLimitsOfShape (Discrete PEmpty) α  → {Discrete}
QuasiFinite α (OreLocalization β γ)   → {OreLocalization}
```
-/
private def structuredPatternHeads (v : Vertex) : HashSet Name :=
  v.pattern.foldl (init := {}) fun s e =>
    if e.getAppArgs.isEmpty then s
    else match e.getAppFn.constName? with
      | some n => s.insert n
      | none => s

/--
Processes a declaration into an edge for the class graph, if appropriate.

---
**Examples**

* **Single-premise instance declaration.** Forgetful instance automatically generated by `class
  Monoid (M : Type u) extends Semigroup M`:

  ```
  -- instance Monoid.toSemigroup {α} [Monoid α] : Semigroup α
  extractEdge? `Monoid.toSemigroup =
    some { src := `Monoid, tgt := `Semigroup }
  ```

* **Multi-premise instance declaration yielding.** Suppose we call `extractEdge?` on the following
  instance declaration:

  ```
  instance Algebra.toModule {R A} {_ : CommSemiring R} {_ : Semiring A} [Algebra R A] : Module R A
  ```

  Despite having multiple premises, this would result in an edge:

  ```
  extractEdge? `Algebra.toModule = some { src := `Algebra, tgt := `Module }
  ```

  The reason for this is that the class `Algebra R A` requires that instances `[CommSemiring R]` and
  `[Semiring A]` be provided. In fact, `Algebra R A` is hiding these instance implicit arguments;
  the fully explicit version would be `@Algebra R A instCommSemiringR instSemiringA`. This is
  established in the class's declaration:

  ```
  class Algebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends SMul R A where
  ```

  Accordingly, whenever we encounter a class hypothesis `[Algebra R A]` in a theorem, we're actually
  seeing `@Algebra R A instCommSemiringR instSemiringA`, meaning that the `{_ : CommSemiring R}` and
  `{_ : Semiring A}` premises of `Algebra.toModule` are satisfied.

* **Instance declaration not yielding any edge because the carrier changes.**

  ```
  -- instance Prod.instMonoid [Monoid M] [Monoid N] : Monoid (M × N)
  extractEdge? `Prod.instMonoid = none -- conclusion is over a new carrier
  ```
-/
public def extractEdge? (name : Name) : MetaM (Option ClassEdge) := do
  let info ← getConstInfo name
  forallTelescopeReducing info.type fun args concl => do
    let some _ ← isClass? concl | return none -- conclusion must be class application
    let mut classPrems : Array Expr := #[]
    for arg in args do
      let argT ← arg.fvarId!.getType
      if (← isClass? argT).isSome then classPrems := classPrems.push arg
      -- if _any_ argument is a proof hypothesis, then this instance is a lost cause
      else if (← isProp argT) then return none
    -- source, if any, must be the last class premise
    let some src := classPrems.back? | return none
    let srcT ← src.fvarId!.getType
    let srcApp ← toKey srcT
    -- A family premise (e.g. `[∀ i, C (f i)]`) is not the same as `C`, so recording `C → tgt` would
    -- be disingenuous.
    if srcApp.familyArity > 0 then return none
    unless ← isWeakeningEdge srcT concl classPrems.pop do return none
    let srcV := srcApp.toVertex
    let tgtV ← toVertex concl
    let srcHeads := structuredPatternHeads srcV
    if (structuredPatternHeads tgtV).any (fun h => !srcHeads.contains h) then return none
    return some { src := srcV, tgt := tgtV }

/-! ## Build -/

/-- The class graph. -/
public structure ClassGraph where
  /-- Array of edges. This is what defines the class graph. -/
  edges : Array ClassEdge
  /--
  `true` iff the vertex's class's codomain is `Prop` or if all applications of the vertex's class
  are subsingletons.
  -/
  isSubsingleton : Vertex → Bool
  /-- Condensation of the class graph. -/
  condensation : Condensation Vertex

/--
For a class with name `name`, return `true` iff any application of this class is a subsingleton.

---
**Background**

Saying that a given class is a subsingleton is somewhat disingenuous. It's actually class
_applications_ that can be subsingletons. If a class's codomain is `Prop`, this distinction doesn't
matter all that much, since we know that any application of the class will be a subsingleton. But if
the class's codomain _isn't_ `Prop`, this distinction can become quite important.

For example, the following synthesizes, i.e., `Module ℤ M` is a subsingleton:

```
variable {M : Type u} [AddCommMonoid M]
#synth Subsingleton (Module ℤ M)
```

Meanwhile, `Module R M`, the "generic" class application of `Module`, does _not_ synthesize, i.e.,
is not a subsingleton:

```
variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M]
#synth Subsingleton (Module R M) -- fails to synthesize
```

When we construct `ClassGraph.isSubsingleton`, we assign a single `Bool` to each vertex, so we need
to make sure that, if we have `ClassGraph.isSubsingleton v == true` for some `v : Vertex`, then any
class application that can match `v` must be a subsingleton. To ensure this, we could try to
synthesize `Subsingleton (…)`, where `…` is the class of `v` applied to arguments of just the right
amount of genericity. For example, if `v` were ``{ name := `Module, pattern := #[ℤ, #0], … }`` (not
actually a vertex in the real class graph, but this is just incidental), then that genericity would
be precisely the one shown in our first code block above. Meanwhile, if `v` were ``{ name :=
`Module, pattern := #[#0, #1], … }``, then that genericity would be the one shown in the second code
block above.

However, having said all this, for the sake of simplicity, we associate subsingleton-ness on a
per-class basis, not on a per-vertex basis. As of Mathlib 4.32.0, the `ClassGraph` of all of Mathlib
does not contain a single vertex for which the `Subsingleton` verdict would change. However, a
per-vertex approach is more principled, and should be considered a (low-priority) opportunity for
future work.
-/
def isSubsingletonClass (name : Name) : MetaM Bool := do
  let r ← withGenericKey name fun app => do
    let goal := mkApp (.const ``Subsingleton [← mkFreshLevelMVar]) app
    unless ← isTypeCorrect goal do return none
    match ← (try trySynthInstance goal catch _ => pure .none) with
    | .some _ => return some true
    | _ => return some false
  return r.getD false

/--
Scans every name in `names` (which is expected to be a list of class and instance declarations),
collecting weakening edges and taking note of subsingleton classes as it goes.

---
**Implementation notes**

This is quite expensive, taking several seconds, and so we try to run it as seldomly as possible.
-/
public def ClassGraph.scanInstances (names : Array Name) :
    MetaM (Array ClassEdge × HashSet Name) := do
  let env ← getEnv
  let mut edges : Array ClassEdge := #[]
  let mut subHeads : HashSet Name := {}
  for name in names do
    if let some e ← extractEdge? name then
      edges := edges.push e
    if let some const := env.find? name then
      let concl := const.type.getForallBody
      if concl.getAppFn.isConstOf ``Subsingleton then
        if let some h := concl.getAppArgs.back?.bind (·.getAppFn.constName?) then
          subHeads := subHeads.insert h
  return (edges, subHeads)

/--
Assembles weakening edges and heads of subsingleton classes into a `ClassGraph`.

---
**Implementation notes**

This function is relatively fast compared to `ClassGraph.scanInstances`, so we re-run it on local
rebuilds.
-/
public def ClassGraph.assemble (edges : Array ClassEdge) (subHeads : HashSet Name) :
    MetaM ClassGraph := do
  let env ← getEnv
  -- We derive the set of vertices by just taking all the endpoints of the edges we collected, which
  -- ensures we don't have isolated vertices (not something that we strictly require, but it doesn't
  -- hurt, since we would never be able to weaken a binder matching an isolated vertex anyway, since
  -- we'd have no edge to weaken it through).
  let vertNames := edges.foldl (init := ({} : HashSet Name)) fun s e =>
    (s.insert e.src.name).insert e.tgt.name
  -- `Prop` subsingletons
  let propClasses := vertNames.fold (init := ({} : HashSet Name)) fun s name =>
    match env.find? name with
    | some const =>
      match const.type.getForallBody with
      | .sort .zero => s.insert name
      | _ => s
    | none => s
  -- Non-`Prop` subsingletons (e.g. `Unique α`)
  let mut subsingletonClasses : HashSet Name := propClasses
  for h in subHeads do
    if vertNames.contains h && !propClasses.contains h then
      if ← isSubsingletonClass h then subsingletonClasses := subsingletonClasses.insert h
  let digraph := edges.foldl (init := ({} : Digraph Vertex)) fun g e => g.insertEdge e.src e.tgt
  return {
    edges,
    isSubsingleton := fun v => subsingletonClasses.contains v.name,
    condensation := digraph.condense
  }

/--
Scans the environment's instances into a `ClassGraph`.
-/
public def ClassGraph.ofEnv : MetaM ClassGraph := do
  let env ← getEnv
  -- Only instances can produce edges. We enforce this restriction because the linter targets
  -- non-explicit binders for weakening, and non-explicit binders are resoved either using instance
  -- synthesis, or unification with instance synthesis as a fallback. So, when we analyze a
  -- declaration, we know that the current binder could be resolved, and we need to make sure that
  -- the weakened version we suggest can also be resolved, which is guaranteed when there's a path
  -- in the class graph from the stronger to the weaker class, precisely because each edge of the
  -- class graph corresponds to an instance that instance synthesis can actually make use of.
  let names := (instanceExtension.getState env).instanceNames.foldl
    (init := (#[] : Array Name)) fun acc name _ => acc.push name
  let (edges, subHeads) ← scanInstances names
  assemble edges subHeads
