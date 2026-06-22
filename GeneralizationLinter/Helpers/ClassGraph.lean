/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
module

public import Lean.Expr
public import Lean.Environment
public import Lean.Meta.Basic
public import Lean.Meta.Instances
public import GeneralizationLinter.Helpers.Vertex
public import GeneralizationLinter.Helpers.Digraph
public import GeneralizationLinter.Helpers.Canonicalization

/-!
# Class Graph

Builds the class graph from the environment.

---
**Main definitions**

* `classifyEdge?`: helper for `extractEdge?` that determines whether an edge
  should be considered `unconditional` or `conditional` (or potentially skipped
  altogether).
* `extractEdge?`: convert an instance into a `ClassEdge`, if appropriate.
* `ofEnv`: build the class graph from the environment.

---
**References**

* [A. J. Best. 2023. _Automatically Generalizing Theorems Using
  Typeclasses_.][best2023automaticallyGeneralizingTheorems]
-/

open Lean Meta

namespace GeneralizationLinter
open Digraph

/-! ## Edges -/

/-- Describes the "conditionality" of an edge of the class graph. -/
public inductive EdgeConditionality
  /-- Unconditional edge; doesn't depend on further conditions. -/
  | unconditional
  /-- Conditional edge; depends on further conditions. -/
  | conditional
  deriving BEq, Hashable, Repr

/-- An edge of the class graph. -/
public structure ClassEdge where
  /-- Source vertex of the edge. -/
  src : Vertex
  /-- Target vertex of the edge. -/
  tgt : Vertex
  /-- Edge conditionality. -/
  conditionality : EdgeConditionality

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
The arguments of a class application that aren't class instances.

---
**Examples**

```
-- class IsPreorder (α : Sort*) (r : α → α → Prop) : Prop
nonInstArgs (@IsPreorder α r) = #[α, r]
-- class CharP (R : Type*) [AddMonoidWithOne R] (p : outParam ℕ) : Prop
nonInstArgs (@CharP R _ p) = #[R, p]
-- class Module (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] : Type (max u v)
nonInstArgs (@Module R M _ _) = #[R, M]
```
-/
public def nonInstArgs (classAppE : Expr) : MetaM (Array Expr) :=
  classAppE.getAppArgs.filterM fun a => return (← isClass? (← inferType a)).isNone

/--
Helper for `extractEdge?` which, given some information about the instance
declaration that `extractEdge?` is processing, indicates the conditionality of
the edge that the extraction will yield. The possible return values are:

* `some unconditional`, returned if the conclusion is a weakening of the source
  over the same data, and needs nothing beyond the source itself.
* `some conditional`, returned if the conclusion is a weakening of the source
  over the same data, but needs an extra premise to hold.
* `none`, returned if the conclusion is not a weakening of the source over the
  same data, or if the conclusion has no carriers.

---
**Examples**

```
-- instance IsPreorder.toIsTrans {α r} [IsPreorder α r] : IsTrans α r
classifyEdge? (IsPreorder α r) (IsTrans α r) #[] = some unconditional

-- instance Module.toDistribMulAction {R M} [Semiring R] [AddCommMonoid M]
--   [Module R M] : DistribMulAction R M
classifyEdge? (Module R M) (DistribMulAction R M) #[Semiring R, AddCommMonoid M] =
  some unconditional

-- instance asymm_of_isTrans_of_irrefl [IsTrans α r] [Std.Irrefl r] : Std.Asymm r
classifyEdge? (Std.Irrefl r) (Std.Asymm r) #[IsTrans α r] = some conditional

-- instance Prod.instMonoid [Monoid M] [Monoid N] : Monoid (M × N)
classifyEdge? (Monoid N) (Monoid (M × N)) #[Monoid M] = none -- different carrier

-- artificial examples
classifyEdge? (IsEmpty α) (IsWellOrder α r) #[] = none -- fresh `r`
classifyEdge? (Std.Irrefl r) (Std.Refl rᶜ) #[] = none -- transformed relation
```
-/
public def classifyEdge? (s t : Expr) (otherPrems : Array Expr) :
    MetaM (Option EdgeConditionality) := do
  -- if target class app has no carriers, reject (e.g., Nat.AtLeastTwo n)
  if (← carrierArgs t).isEmpty then return none
  -- weakening if all of target's non-inst args are defeq to some arg of source
  let sArgs ← nonInstArgs s
  let tArgs ← nonInstArgs t
  let weakening ← tArgs.allM fun tArg => sArgs.anyM fun sArg => isDefEq tArg sArg
  unless weakening do return none -- if not a weakening, reject
  -- conditional if there are premises that are not already provided by the source
  let allSrcArgs := s.getAppArgs
  let conditional := otherPrems.any fun p => !allSrcArgs.contains p
  return some (if conditional then .conditional else .unconditional)

/--
Processes a declaration into an edge for the class graph, if appropriate.

---
**Examples**

* **Single-premise instance declaration.** Forgetful instance automatically
  generated by `class Monoid (M : Type u) extends Semigroup M`:

  ```
  -- instance Monoid.toSemigroup {α} [Monoid α] : Semigroup α
  extractEdge? `Monoid.toSemigroup =
    some { src := `Monoid, tgt := `Semigroup, conditionality := unconditional }
  ```

* **Multi-premise instance declaration yielding unconditional edge.** Suppose we
  call `extractEdge?` on the following instance declaration:

  ```
  instance Algebra.toModule {R A} {_ : CommSemiring R} {_ : Semiring A} [Algebra R A] : Module R A
  ```

  Despite having multiple premises, this would result in an unconditional edge:

  ```
  extractEdge? `Algebra.toModule = some { src := `Algebra, tgt := `Module,
    conditionality := unconditional }
  ```

  The reason for this unconditionality is that the class `Algebra R A` requires
  that instances `[CommSemiring R]` and `[Semiring A]` be provided. In fact,
  `Algebra R A` is hiding these instance implicit arguments; the fully explicit
  version would be `@Algebra R A instCommSemiringR instSemiringA`. This is
  established in the class's declaration:

  ```
  class Algebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends SMul R A where
  ```

  Accordingly, whenever we encounter a class hypothesis `[Algebra R A]` in a
  theorem, we're actually seeing `@Algebra R A instCommSemiringR instSemiringA`,
  meaning that the `{_ : CommSemiring R}` and `{_ : Semiring A}` premises of
  `Algebra.toModule` are satisfied.

* **Conditional edge.** Calling `extractEdge?` on the instance declaration below
  yields a conditional edge:

  ```
  instance asymm_of_isTrans_of_irrefl [IsTrans α r] [Std.Irrefl r] : Std.Asymm r
  ```

  To see why, take a look at how the classes of the premises of the declaration
  are defined:

  ```
  class Irrefl (r : α → α → Prop) : Prop where
    irrefl : ∀ a, ¬r a a
  class IsTrans (α : Sort*) (r : α → α → Prop) : Prop where
    trans : ∀ a b c, r a b → r b c → r a c
  ```

  Since `Std.Irrefl` doesn't require `IsTrans`, the `[IsTrans α r]` hypothesis
  of `asymm_of_isTrans_of_irrefl` is a genuine additional premise that needs to
  be satisfied for the edge to be sound, which is why the extracted edge is
  considered conditional.

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
      else if (← isProp argT) then return none
    -- source = the last class premise (heuristic)
    let some src := classPrems.back? | return none
    let srcT ← src.fvarId!.getType
    let some conditionality ← classifyEdge? srcT concl classPrems.pop | return none
    return some { src := ← toVertex srcT, tgt := ← toVertex concl, conditionality }

/-! ## Build -/

/-- The class graph. -/
public structure ClassGraph where
  /-- Array of edges. This is what defines the class graph. -/
  edges : Array ClassEdge
  /-- `true` iff the vertex's codomain is `Prop`. -/
  isProofIrrelevant : Vertex → Bool
  /-- Condensation of the class graph when limited to `unconditional` edges. -/
  unconditionalCondensation : Condensation Vertex
  /-- Condensation of the class graph, including `conditional` edges. -/
  fullCondensation : Condensation Vertex

namespace ClassGraph

/--
Scans the environment's instances into a `ClassGraph`.
-/
public def ofEnv : MetaM ClassGraph := do
  let env ← getEnv
  let names := (instanceExtension.getState env).instanceNames.foldl
    (init := (#[] : Array Name)) fun acc name _ => acc.push name
  let edges ← names.filterMapM extractEdge?
  let vertNames := edges.foldl (init := ({} : Std.HashSet Name)) fun s e =>
    (s.insert e.src.name).insert e.tgt.name
  let propClasses := vertNames.fold (init := ({} : Std.HashSet Name)) fun s name =>
    match env.find? name with
    | some ci =>
      match codomainOf ci.type with
      | .sort .zero => s.insert name
      | _ => s
    | none => s
  let build := fun (keep : EdgeConditionality → Bool) =>
    (edges.filter (keep ·.conditionality)).foldl (init := ({} : Digraph Vertex)) fun g e =>
      g.insertEdge e.src e.tgt
  return {
    edges,
    isProofIrrelevant := fun v => propClasses.contains v.name,
    unconditionalCondensation := (build (· == .unconditional)).condense,
    fullCondensation := (build (fun _ => true)).condense
  }


/-! ## Resolution -/

/-- Which edges a resolution pass should admit. -/
public inductive Admit
  /-- Admit all edges (optimistic). -/
  | all
  /-- Only admit `unconditional` edges (conservative). -/
  | unconditional

/--
The condensation of `G` under a given `Admit` policy.
-/
public def resolve (G : ClassGraph) (a : Admit) : Condensation Vertex :=
  match a with
  | .unconditional => G.unconditionalCondensation
  | .all => G.fullCondensation
