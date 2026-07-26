/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
module

public import Lean.Expr
public import Lean.Environment
public import Lean.Meta
public import GeneralizationLinter.Graph.Digraph
public import GeneralizationLinter.Graph.Vertex
public import GeneralizationLinter.Graph.Canonicalization

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
Returns `true` iff `a`'s type is or reduces to `Sort`.
-/
public def isSortTyped (a : Expr) : MetaM Bool :=
  -- `whnfR` sees through reducible binder gadgets like `semiOutParam` or `outParam`; e.g., `RCLike`
  -- binds `(K : semiOutParam (Type*))`, so plain `(← inferType K).isSort` would return `false`,
  -- while `(← whnfR (← inferType K)).isSort` returns `true`.
  return (← whnfR (← inferType a)).isSort


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
Returns `true` iff `e` is "statable" from `sArgs`.

We define statability inductively as follows: `e` is statable from `sArgs` if

1.  `whnfR e` is syntactically equal to `whnfR sArgs[i]` for some `i`,
2.  `whnfR e` is an fvar occurring in `whnfR sArgs[i]` for some `i`,
3.  `whnfR e` is "closed" according to `isClosed` (intuitively, this means it contains no fvars), or
4.  `whnfR e` is an application of a "non-synonym" type former to arguments that are statable from
    `sArgs`.

By synonym type former we mean any type former which unfolds to one of its own arguments. By
"non-synonym" type formers we mean any other type former. For example, `OrderDual` is a synonym type
former, while `Monoid` is a "non-synonym" type former. See also `isSynonymFormer`.

---
**Implementation notes**

One could argue that condition 2 should be weakened to `whnfR e` being an fvar that occurs in
`sArgs[i]` instead of `whnfR sArgs[i]`. For example, if `sArgs[i]` is `FirstOf α β`, where `FirstOf
α β := α`, and `whnfR e` is `β`, the weakened version would claim that `β` is statable from `FirstOf
α β`, while the original condition 2 claims that it is not. However, condition 2, as stated, is
better-suited for our purposes. This is because `canonArg` also uses `whnfR`, meaning that an
application like `Monoid (FirstOf α β)` would be canonicalized into `Monoid α`. Hence, an instance
like `instance Monoid (FirstOf α β) : Magma β` (let's pretend that it makes sense) would be
extracted into an (unsound) edge from `Monoid α` to `Magma β` under the weakened condition 2, and
rejected under the original condition 2.

---
**Examples**

According to our definition of "statable", we have the following (where `α` and `β` are fvars):

**Definition case 1:**
* `α` is statable from `#[α]`.
* `Monoid α` is statable from `#[Monoid α]`.
* `OrderDual α` is statable from `#[OrderDual α]`.

**Definition case 2:**
* `α` is statable from `#[Monoid α]`.
* `α` is statable from `#[OrderDual α]`.

**Definition case 3:**
* `ℕ` is statable from `#[]`.
* `Monoid ℕ` is statable from `#[]`.

**Definition case 4:**
* `Monoid α` is statable from `#[α]`.

**Definition cases 2 and 4:**
* `Monoid α` is statable from `#[Group α]`.

**Non-examples:**
* `α` is not statable from `#[]` or `#[β]`.
* `Monoid α` is not statable from `#[]` or `#[β]`.
* `α` is not statable from `#[Monoid α]`.
* `OrderDual α` is not statable from `#[α]`.

**Note:** The reason we claim that `OrderDual α` is not statable from `#[α]`, while at the same time
claiming that `α` is statable from `#[OrderDual α]`, is that we don't want to introduce synonyms,
but are okay with removing them.
-/
public partial def statableFrom (sArgs : Array Expr) (isClosed : Expr → MetaM Bool)
    (e : Expr) : MetaM Bool := do
  go (← sArgs.mapM whnfR) e
where go (sArgs : Array Expr) (e : Expr) : MetaM Bool := do
  let e ← whnfR e
  if sArgs.contains e then return true
  if e.isFVar then return sArgs.any (·.containsFVar e.fvarId!)
  if ← isClosed e then return true
  let fn := e.getAppFn
  let some head := fn.constName? | return false
  if ← isSynonymFormer head then return false
  unless isTypeConstructor (← getEnv) fn do return false
  (← frameArgs e).allM (go sArgs)


/--
Helper for `extractEdge?` which, given some information about the instance declaration that
`extractEdge?` is processing, indicates whether the edge is a weakening edge, which is the case iff
all of the following conditions are satisfied:

1.  Every frame argument of the target is statable from the source's arguments (see also
    `statableFrom`).

    **Why?** Our graph's edges are ordered pairs of vertices, each vertex representing a specific
    kind of class application. For the graph to be sound, wee need each edge to guarantee that,
    given the source vertex, we can reach the target vertex. If the target is not statable from the
    source's arguments, then this cannot be the case.

2.  Every class-typed argument of the declaration other than the source is contained in the source's
    type as a direct argument.

    **Why?** The rationale is essentially the same as for condition 1, this is just the analog for
    class-typed args. Together, frame arguments and class-typed arguments comprise all arguments of
    an instance (unless there's a non-class-typed instance-implicit parameter, which is almost never
    the case; Mathlib has only one such declaration, `CategoryTheory.Bundled.of`, and even there the
    intended usage is that the instance-implicit parameter should be a typeclass). They may also
    overlap; for example, there's plenty of class-typed implicit arguments in Mathlib (see e.g.
    `IsTopologicalGroup.toContinuousInv` in the examples section below).

For a brief discussion on this topic, see the thread [_general > When are instance mappings
projections_](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/When.20are.20instance.20mappings.20projections)
on the Lean Zulip.

---
**Examples**

(Note: In the examples below, "source" refers to the last argument of the instance, which is looser
than the sense in which the term is used for `sourceArg?`.)

| Instance | Source's args | Target's frame args | C1 |
|:--- |:--- |:--- |:--- |
| `IsTopologicalGroup.toContinuousInv` | `G`, `inst₁`, `inst₂`, `self` | `G` | ✓ |
| `Semiring.toNatAlgebra` | `R`, `inst` | `ℕ`, `R` | ✓ |
| `ULift.addLeftCancelMonoid` | `α`, `inst` | `ULift α` | ✓ |
| `Lex.instIsRightCancelAdd` | `α`, `inst₁`, `inst₂` | `Lex α` | ✗ |
| `Matrix.isScalarTower` | `R`, `S`, `α`, `inst₁`, `inst₃`, `inst₂` | `R`, `S`, `Matrix m n α` | ✗ |
| `IsNoetherianRing.wfDvdMonoid` | `R`, `inst₁` | `R` | ✓ |

| Instance | Class-typed args…¹ | Source's type | C2 |
|:--- |:--- |:--- |:--- |
| `IsTopologicalGroup.toContinuousInv` | `inst₁`, `inst₂` | `@IsTopologicalGroup G inst₁ inst₂` | ✓ |
| `Semiring.toNatAlgebra` | _(none)_ | `@Semiring R` | ✓ |
| `ULift.addLeftCancelMonoid` | _(none)_ | `@ULift α` | ✓ |
| `Lex.instIsRightCancelAdd` | `inst₁` | `@IsRightCancelAdd α inst₁` | ✓ |
| `Matrix.isScalarTower` | `inst₁`, `inst₂`, `inst₃` | `@IsScalarTower R S α inst₁ inst₃ inst₂` | ✓ |
| `IsNoetherianRing.wfDvdMonoid` | `inst₁`, `inst₂` | `@IsNoetherianRing R (CommSemiring.toSemiring R inst₁)` | ✗ |

¹Class-typed args of the declaration other than the source.

```
instance IsTopologicalGroup.toContinuousInv {G : Type*} {inst₁ : TopologicalSpace G}
  {inst₂ : Group G} [self : @IsTopologicalGroup G inst₁ inst₂] : ContinuousInv G
instance Semiring.toNatAlgebra {R : Type*} [inst : @Semiring R] : Algebra ℕ R
instance ULift.addLeftCancelMonoid {α : Type*}
  [inst : @AddLeftCancelMonoid α] : AddLeftCancelMonoid (ULift α)
instance Lex.instIsRightCancelAdd {α : Type*} [inst₁ : Add α]
  [inst₂ : @IsRightCancelAdd α inst₁] : IsRightCancelAdd (Lex α)
instance Matrix.isScalarTower {m n R S α : Type*}
  [inst₁ : SMul R S] [inst₂ : SMul R α] [inst₃ : SMul S α]
  [inst₄ : @IsScalarTower R S α inst₁ inst₃ inst₂] : IsScalarTower R S (Matrix m n α)
instance IsNoetherianRing.wfDvdMonoid {R : Type u_1} [inst₁ : CommSemiring R]
  [inst₂ : @IsDomain R (@CommSemiring.toSemiring R inst₁)]
  [inst₃ : @IsNoetherianRing R (@CommSemiring.toSemiring R inst₁)] : WfDvdMonoid R
```
-/
public def isWeakeningEdge (s t : Expr) (otherPrems : Array Expr) :
    MetaM Bool := do
  let sArgs := s.getAppArgs
  let tArgs ← frameArgs t
  let isClosed (e : Expr) : MetaM Bool := pure (!e.hasFVar && !e.hasExprMVar)
  -- Condition 1
  unless ← tArgs.allM (statableFrom sArgs isClosed) do return false
  -- Condition 2: Every class-typed arg of declaration (other than `s`) must be contained in `s`'s
  -- type.
  return otherPrems.all fun p => sArgs.contains p


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
    let srcK ← toKey srcT
    -- A family premise (e.g. `[∀ i, C (f i)]`) is not the same as `C`, so recording `C → tgt` would
    -- be disingenuous.
    if srcK.familyArity > 0 then return none
    unless ← isWeakeningEdge srcT concl classPrems.pop do return none
    let tgtK ← toKey concl
    -- Opaque carriers, i.e., carriers whose structure `canonArg` could not preserve, are abstracted
    -- to bvars, lead to `subst` entries that aren't just fvars. For example: `Class1 (Class2 α)`
    -- (not opaque) gets `pattern := #[Class2 (bvar 0)]` and `subst := #[α]`, while
    -- `Class1 (OpaqueSomething α)` gets `pattern := #[bvar 0]` and `subst := #[OpaqueSomething α]`.
    -- We don't want to accept this latter kind of target. The same goes for the source.
    unless srcK.subst.all (·.isFVar) && tgtK.subst.all (·.isFVar) do return none
    return some { src := srcK.toVertex, tgt := tgtK.toVertex }


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
def isSubsingletonClass (name : Name) (synthesize : Bool := true) : MetaM Bool := do
  let r ← withGenericKey name fun app body => do
    -- `withGenericKey` already whnf-reduced `body` for us.
    if body.isProp then return some true
    unless synthesize do return some false
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
  -- We derive the set of vertices by just taking all the endpoints of the edges we collected, which
  -- ensures we don't have isolated vertices (not something that we strictly require, but it doesn't
  -- hurt, since we would never be able to weaken a binder matching an isolated vertex anyway, since
  -- we'd have no edge to weaken it through).
  let vertNames := edges.foldl (init := ({} : HashSet Name)) fun s e =>
    (s.insert e.src.name).insert e.tgt.name
  let mut subsingletonClasses : HashSet Name := {}
  for name in vertNames do
    let worthSynthesizing := subHeads.contains name
    if ← isSubsingletonClass name (synthesize := worthSynthesizing) then
      subsingletonClasses := subsingletonClasses.insert name
  let digraph := edges.foldl (init := ({} : Digraph Vertex)) fun g e => g.insertEdge e.src e.tgt
  return {
    edges,
    isSubsingleton := fun v => subsingletonClasses.contains v.name,
    condensation := digraph.condense
  }
