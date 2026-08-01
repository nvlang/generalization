/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
module
public import GeneralizationLinter.Graph.ClassGraph
public import GeneralizationLinter.Analysis.Collect
public import GeneralizationLinter.Analysis.Options

open Lean Meta

namespace GeneralizationLinter
open Digraph Digraph.Condensation
open Std (HashSet HashMap)

/-! # Candidates -/

/-- The kinds of possible weakening suggestions. -/
public inductive WeakeningShape where
  /--
  Binder may be droppable: as far as the linter can tell, nothing requires it, or everything it
  would have to provide is already available without it.
  -/
  | drop
  /-- Binder may be weakenable to `weakerVertex`. -/
  | weaken (weakerVertex : Vertex)
  /-- Binder may be weakenable by splitting it up into `weakerVertices`. -/
  | split (weakerVertices : Array Vertex)
deriving Inhabited


/-- An unverified weakening candidate. -/
public structure Candidate where
  /-- The binder this candidate proposes weakening. -/
  binder : TargetedBinder
  /-- The kind of weakening this candidate proposes. -/
  shape : WeakeningShape
deriving Inhabited


/-- The `Vertex`es of the classes of the proposed replacements. -/
public def Candidate.replacements (c : Candidate) : Array Vertex :=
  match c.shape with
  | .drop => #[]
  | .weaken t => #[t]
  | .split ts => ts


/--
Things that we need to compute the minimal common ancestors, or things which may affect said
computation, compiled into one structure.
-/
private structure MCAContext where
  /-- Class graph. -/
  graph : ClassGraph
  /-- See `AbsencePolicy`. -/
  absencePolicy : AbsencePolicy
  /-- See `SplitPolicy`. -/
  splitPolicy : SplitPolicy
  /-- Subsumption in vertex matching. -/
  includeSubsumers : Bool


/--
If `ctx.includeSubsumers = true`:
* Returns `true` iff `u` (or a subsumer thereof) reaches `v` (or a subsumer thereof) in `ctx.graph`.

If `ctx.includeSubsumers = false`:
* Returns `true` iff `u` reaches `v` in `ctx.graph`.
* Note: if neither `u` nor its universe-polymorphic variant is in the class graph, or the same holds
  of `v`, then this function will inevitably return `false` (even if `u = v`).

**Note:** In all of these cases, "`u` reaches `v`" is to be understood as "`u` (or, if `u`'s
universe levels are concrete, its universe-polymorphic variant) reaches `v` (or, if `v`'s universe
levels are concrete, its universe-polymorphic variant)".

---
**Examples**

```
ctx.reachesWitnessed (Monoid #0) (Semigroup #0) = true
ctx.reachesWitnessed (Semigroup #0) (Monoid #0) = false
ctx.reachesWitnessed (Monoid #0) (Monoid (MulOpposite #0)) = true
ctx.reachesWitnessed (Monoid.{0} #0) (Monoid.{0} #0) = true -- neither is a class graph vertex
```
-/
def MCAContext.reachesWitnessed (ctx : MCAContext) (u v : Vertex) : Bool :=
  (u.witnesses ctx.includeSubsumers).any fun u' =>
    (v.witnesses ctx.includeSubsumers).any fun v' => ctx.graph.condensation.reaches u' v'

/--
Returns `true` iff `u` and `v` can be unified.

**Note:** We use syntactic equality in this process, so e.g. `OrderDual ℕ` does not unify with `ℕ`
according to us, even though Lean's actual unification mechanism _would_ unify them, since it uses
definitional equality.

---
**Examples**

```
Vertex.unifiable (Monoid #0) (Semigroup #0) = false
Vertex.unifiable (Pow #0 ℕ) (Pow #0 ℤ) = false
Vertex.unifiable (Pow #0 ℕ) (Pow #0 #1) = true
Vertex.unifiable (Module #0 #0) (Module #0 #1) = true
Vertex.unifiable (Module #0 #0) (Module #0 (MulOpposite #0)) = false
```
-/
public partial def Vertex.unifiable (u v : Vertex) : Bool :=
  -- If the vertices aren't of the same classes, then they can't be unified.
  if u.name != v.name then false else
    -- Find largest bvar index (plus one) across elements of `u.pattern`.
    let offset := u.pattern.foldl (fun n e => max n e.looseBVarRange) 0
    -- Offset bvar indices in `v.pattern` and zip the two patterns, checking if they can be unified
    -- together element by element, keeping track of constraints in `σ`. The result of the `foldlM`
    -- call is `some σ` if `u.pattern` and `v.pattern` can be unified with constraints `σ`, and
    -- `none` if they can't be unified.
    ((u.pattern.zip (v.pattern.map (Expr.liftLooseBVars · 0 offset))).foldlM
      (fun σ (x, y) => unifyPatterns σ x y) ({} : HashMap Nat Expr)).isSome
where
  /-- Does bvar index `i` occur in an expression, given constraints `σ`? -/
  occursIn (σ : HashMap Nat Expr) (i : Nat) : Expr → Bool
    | .bvar j =>
      -- Expression is `.bvar j`, so it contains bvar index `i` if `i = j`,
      i == j ||
      -- or if `.bvar j` is constrained to some other expression that contains bvar index `i`.
      (σ[j]?.map (occursIn σ i)).getD false
    -- Recurse into application heads and arguments.
    | .app fn arg => occursIn σ i fn || occursIn σ i arg
    -- Besides bvars and applications, patterns only contain closed subterms (constants, nat
    -- literals, sorts), which never contain bvars, so if we reach this point we know that the
    -- expression doesn't contain any bvar at all.
    | _ => false
  /-- Given constraints `σ` mapping bvar indices to `Expr` values they are required to have, see if
      two expressions can be unified, and return the updated constraints map if so. -/
  unifyPatterns (σ : HashMap Nat Expr) : Expr → Expr → Option (HashMap Nat Expr)
    | .bvar i, e
    | e, .bvar i =>
      -- Examples: `.bvar 0, .bvar 1`, `ℕ, .bvar 1`, etc.
      match σ[i]? with -- Is `.bvar i` constrained?
      -- Yes ⟹ Unfold `.bvar i` to whatever it's constrained to and check `e` against that.
      | some t => unifyPatterns σ t e
      -- No ⟹ `.bvar i` is not constrained (thus far).
      | none =>
        -- If `e` is also just `.bvar i`, then this step doesn't introduce any new constraints.
        if e == .bvar i then some σ
          -- If `.bvar i` occurs in `e` but is not equal to it, unification would require an
          -- infinite loop, which we don't support.
          else if occursIn σ i e then none
          -- Record the constraint `.bvar i ↦ e`.
          else some (σ.insert i e)
    -- Two applications can be unified if their heads can be unified and their arguments can be
    -- unified, all using the same constraints.
    | .app f x, .app g y => (unifyPatterns σ f g).bind fun σ => unifyPatterns σ x y
    -- A closed subterm can be unified with an expression iff the latter is equal to the former.
    -- Since patterns only contain bvars, applications, and closed subterms (constants, nat
    -- literals, sorts), at least one of `a` or `b` has to be closed at this point, so `a` and `b`
    -- are unifiable iff they're equal.
    -- Note that we use syntactic equality, so e.g. `OrderDual ℕ` does not unify with `ℕ` according
    -- to us, even though Lean's actual unification mechanism _would_ unify them, since it uses
    -- definitional equality.
    | a, b => if a == b then some σ else none


/--
Return the data-carrying (i.e., non-subsingleton) descendants of `v` in `ctx.graph`. Note that, if
`v` was data-carrying, it would be among the returned descendants.

---
**Examples**

```
ctx.dataDescendants (Star #0) = #[Star #0, Star (MulOpposite #0)]
ctx.dataDescendants (Monoid (MulOpposite #0)) = #[Monoid (MulOpposite #0), Monoid (DomMulAct #0)]
ctx.dataDescendants (Std.IsPreorder #0) = #[]
```
-/
def MCAContext.dataDescendants (ctx : MCAContext) (v : Vertex) : Array Vertex :=
  let cond := ctx.graph.condensation
  match cond.componentsMap[v]? with
  | none => #[]
  | some sccᵥ => (cond.downSetsByIndex.getD sccᵥ {}).toArray.foldl (init := #[]) fun sccMembersᵥ sccDesc =>
      (cond.members.getD sccDesc #[]).foldl (init := sccMembersᵥ) fun dataDescsᵥ desc =>
        if ctx.graph.isSubsingleton desc then dataDescsᵥ else dataDescsᵥ.push desc


/--
Returns `true` iff, within `ctx.graph`, `u` and `v` (or any subsumers thereof) share a data-carrying
(i.e., non-subsingleton) descendant.

In our case, this is used to determine whether a class hypothesis `h` could be split into two class
hypotheses `h₁` and `h₂`. If `h₁` and `h₂` share a data-carrying descendant in the class graph, then
the answer is no, because splitting `h` into `h₁` and `h₂` could allow `h₁` and `h₂` to each use a
different instance of the data that was previously solely carried by `h`, which could change the
meaning of the declaration being processed. If `h₁` and `h₂` only share non-data-carrying
descendants, splitting `h` into `h₁` and `h₂` is safe, due to proof irrelevance. Similarly, if `h₁`
and `h₂` don't share any descendants, splitting `h` into `h₁` and `h₂` is also safe.

**Warning:** Even if `sharesDataDesc` returns `false`, splitting a class hypothesis may still
introduce a diamond. This is because our class graph's encoding of instance mappings is lossy, and
doesn't keep track of the relations between the bound variables of one vertex and another under any
given instance mapping.

_See also:_ Alex J. Best. 2023. Automatically Generalizing Theorems Using Typeclasses. In Fifth
Workshop on Formal Mathematics for Mathematicians. CEUR Workshop Proceedings.
Retrieved from [https://ceur-ws.org/Vol-3377/fmm12.pdf](https://ceur-ws.org/Vol-3377/fmm12.pdf).


---
**Examples**

* `sharesDataDesc` would return `true` for `Semigroup` and `MulOneClass`, since those two classes
  share the data-carrying descendant `Mul`. This means that a theorem with hypothesis `[Monoid α]`
  but which uses only `[Semigroup α]` and `[MulOneClass α]` can nonetheless not split the `Monoid`
  hypothesis up, because the instances of `Mul` that `Semigroup` and `MulOneClass` each use would
  not be guaranteed to be the same anymore.
* `sharesDataDesc` would return `false` for `IsPreorder` and `Std.Total`, since those two classes
  only share the non-data-carrying descendants such as `Std.Refl`. This means that a theorem with
  hypothesis `[IsLinearOrder r]` but which uses only `[IsPreorder r]` and `[Std.Total r]` could
  safely split the `IsLinearOrder` hypothesis up, because the instances of `Std.Refl` that
  `IsPreorder` and `Std.Total` each use are guaranteed to be equal due to proof irrelevance.
-/
def MCAContext.sharesDataDesc (ctx : MCAContext) (u v : Vertex) : Bool :=
  (u.witnesses ctx.includeSubsumers).any fun u' =>
    let descsᵤ := ctx.dataDescendants u'
    (v.witnesses ctx.includeSubsumers).any fun v' =>
      let descsᵥ := ctx.dataDescendants v'
      descsᵤ.any fun dᵤ => descsᵥ.any (Vertex.unifiable dᵤ ·)

/--
Applies two filters to `reqVerts` and returns the result. The filters are:
1.  Every bvar of a requirement's `pattern` must be substitutable via the binder's `Key.subst`.
2.  Requirements that are strictly weaker than another requirement are dropped.

---
**Examples**

```
-- `b` is the binder `[Monoid α]`, so `b.subst = #[α]`
ctx.filterReqVerts b {Monoid #0, Semigroup #0, Mul #0, Module #0 #1} = #[Monoid #0]
ctx.filterReqVerts b {Module #0 #1} = #[]
```
-/
def MCAContext.filterReqVerts (ctx : MCAContext) (b : TargetedBinder)
    (reqVerts : HashSet Vertex) : Array Vertex :=
  -- Filter 1.
  let reqVerts' := reqVerts.toArray.filter (fun v => v.pattern.all (·.looseBVarRange ≤ b.subst.size))
  -- Filter 2.
  reqVerts'.filter fun u =>
    ¬ reqVerts'.any fun v => v != u && ctx.reachesWitnessed v u && ¬ ctx.reachesWitnessed u v


/--
These are class names that Mathlib has access to but which, if found within an SCC, have preferred
alternatives.
-/
def sccDemotedHeads : List Name := [`NSMul, `ZSMul, `NPow, `ZPow, `OfNat, `Trans]

/--
The deterministic "algorithm" by which we pick representatives when `sccDemotedHeads` doesn't
already force our decision. We also use this to choose a minimal common ancestor when
`minCommonAncestors` would otherwise return multiple.

---
**Examples**

```
minByName? #[Semigroup #0, Mul #0, Monoid #0] = some (Monoid #0)
minByName? #[OfNat #0 1, One #0] = some (OfNat #0 1)
minByName? #[] = none
```
-/
def minByName? (vertices : Array Vertex) : Option Vertex :=
  vertices.foldl (init := none) fun best v => match best with
    | none => some v
    | some w => if (v.name.cmp w.name).isLT then some v else some w

/--
Deterministically picks a vertex within a given SCC, avoiding any vertex whose `Vertex.name` is in
`sccDemotedHeads`.

---
**Examples**

```
sccRepresentative? #[OfNat #0 1, One #0] = some (One #0)
sccRepresentative? #[OfNat #0 1] = some (OfNat #0 1)
sccRepresentative? #[] = none
```
-/
def sccRepresentative? (scc : Array Vertex) : Option Vertex :=
  minByName? (scc.filter fun v => !sccDemotedHeads.contains v.name) <|> minByName? scc


/--
Returns a minimal common ancestor (MCA) of `reqVerts` in `ctx.graph.condensation` which `b` can
reach. If none exists, returns `none`. If more than one such MCA exists, uses `minByName?` to
tie-break incomparable MCAs, and `sccRepresentative?` to tie-break the comparable ones (which will
inevitably be equipotent).

---
**Implementation notes**

`reqVerts` contains "vertices", but they're not necessarily in the class graph; they're just
applications canonicalized to `Vertex` so that we can query the class graph with them. We call these
vertices "witnesses", as each one represents a "witness" for a specific requirement of a theorem.

If any `reqVert` in `reqVerts` happened to canonicalize to a `Vertex` that isn't actually in the
class graph (which may well be the case, as the class graph has strict inclusion criteria (and even
if it didn't it's still just based off of registered instances, and a theorem can have class
applications of whatever kind it wants)), `minCommonAncestors` would query the class graph for
`reqVert` (via `reqVerts.map condensation.indicesOf`) and find nothing, which `minCommonAncestors`
doesn't like because it essentially means that there's a requirement that it can't take into
account, i.e., that is "absent" from the class graph. When `AbsencePolicy` is `failClosed`, which is
its default, then that means `minCommonAncestors` will just play it safe and return `#[]`. But even
if `AbsencePolicy` were `failOpenGuarded` it wouldn't fix our problems, as `minCommonAncestors` in
that case could easily return an ancestor which doesn't satisfy the unaccounted-for requirement,
which would then just lead to the verification pipeline rejecting the suggestion, costing us time
and quite possibly recall.

So instead what we do is expand `reqVert` into a set `{req, subsumer₁, …, subsumerₙ}` of `Vertex`
records (which in this context we call "witnesses"; see also `minCommonAncestors`'s docstring) which
includes any subsumer of `reqVert`. These subsumers aren't guaranteed to match a class graph vertex
either, but it significantly increases our chances, and is still perfectly sound because any
ancestor that satisfies a subsumer of `reqVert` would also satisfy `reqVert`.

**Example:** If `reqVert` is `Membership #0 (Submodule #1 #0)` (a real requirement of
`Submodule.span_range_subtype_eq_top_iff`), then just querying the class graph for `reqVert` would
return nothing; `reqVert` is simply not _in_ the class graph. Meanwhile, if we first expanded
`reqVert` to `reqVert.witnesses = #[reqVert, Membership #0 #1, Membership #0 (Submodule #1 #2)]`,
we'd find that `Membership #0 #1` _is_ a vertex of the class graph and hence something that
`minCommonAncestors` can use. Finally, an ancestor which satisfies `Membership #0 #1` is also
guaranteed to satisfy `Membership #0 (Submodule #1 #0)` (note that the `#0` etc. are bvars, meaning
that the `#0` in `Membership #0 #1` does _not_ have to refer to the same thing as the `#0` in
`Membership #0 (Submodule #1 #0)`). In this specific case, this corresponds to the intuition that,
if something can define `∈` between _any_ two things, it can surely define it between `α` and
`Submodule β α` for any `α β : Type*`.

**Note:** `reqVert.witnesses` also helps out with universe polymorphism; if `reqVert` is pinned to
some specific universes, it's rather unlikely that it'll be a vertex in the class graph, but
`reqVert.witnesses` also returns `Vertex` records which correspond to `reqVert` or one of its
subsumers in every way except also being universe polymorphic.

**See also:** `minCommonAncestors`.
-/
def MCAContext.minCommonAncestor? (ctx : MCAContext) (b : TargetedBinder) (reqVerts : Array Vertex) :
    Option Vertex :=
  -- De-duplicate, and include vertices that match requirements too if `includeSubsumers` is `true`,
  -- converting `reqVerts` into an array of sets, which will be interpreted by `minCommonAncestors`
  -- as an AND of ORs to satisfy.
  let witnessSets := reqVerts.map
    fun reqVert => HashSet.ofArray (reqVert.witnesses ctx.includeSubsumers)
  -- Only MCAs that `b` can reach are of interest to us, otherwise they're not weakenings of `b`.
  let mcas := (ctx.graph.condensation.minCommonAncestors witnessSets ctx.absencePolicy).filter
    fun scc => scc.any (ctx.reachesWitnessed b.toVertex ·)
  match mcas with
  | #[] => none
  | #[scc] => sccRepresentative? scc
  -- #TODO (low priority): If `mcas` has size ≥2, it means there's multiple incomparable minimal
  -- common ancestors, each of which single-handedly satisfies all requirements (see
  -- `minCommonAncestors`'s docstring for an example). We could try to simply present them as
  -- multiple viable options (after verifying them, of course). For now, we just pick one ancestor
  -- from `mcas` according to the deterministic procedure implemented by `minByName?` and go with
  -- that.
  -- This shouldn't happen all that often anyway, so any further improvements here should be
  -- considered relatively low-priority.
  | sccs => minByName? (sccs.filterMap sccRepresentative?)

/-- Is `b` strictly stronger than `v` according to `ctx.graph`? -/
def MCAContext.strictlyStrongerThan (ctx : MCAContext) (b : TargetedBinder) (v : Vertex) :
    Bool :=
  let bVertex := b.toVertex
  v != bVertex && ctx.reachesWitnessed bVertex v && ¬ ctx.reachesWitnessed v bVertex


/--
Partition `reqVerts` into non-data-descendant-sharing blocks and return the MCAs of the blocks as an
array, or `none` if
* `reqVerts` can't be split up, or
* if any of the blocks don't have a MCA, or
* if any of the blocks' MCAs are not strictly weaker than `b` (in which case we'd be e.g. replacing
  `[Group G]` with `[Group G] […]`, which would be pointless), or
* if the MCAs share any data-carrying descendant.

**Note:** This function only ever gets called when `splitPolicy` is `.allow` or `.prefer`.
-/
def MCAContext.mcasPartition? (ctx : MCAContext) (b : TargetedBinder) (reqVerts : Array Vertex) :
    Option (Array Vertex) := Id.run do
  let blocks := partitionByDesc (HashSet.ofArray reqVerts) ctx.sharesDataDesc
  if blocks.size ≤ 1 then return none -- If `reqVerts` can't be split up, return `none`.
  let mut mcas : Array Vertex := #[]
  for block in blocks do
    let some mca := ctx.minCommonAncestor? b block.toArray | return none
    unless ctx.strictlyStrongerThan b mca do return none
    -- `mcas` may contain duplicates. Consider the following example: `IsAlmostIntegral.coeff`'s
    -- `[IsDomain R]` binder has three requirements imposed on it: `Nontrivial #0`, `NoZeroDivisors
    -- #0`, and `NoZeroDivisors (Polynomial #0)`. Now, first, we partition these three requirements
    -- into `blocks`; since none of them share a data descendant with any of the other (they're all
    -- `Prop`-valued), we get three distinct blocks, and hence will call `minCommonAncestor?` three
    -- times. Now, within `minCommonAncestor?`, each member of each block is expanded into a witness
    -- set:
    --
    -- * `ctx.minCommonAncestor? {Nontrivial #0} ≈ ctx.graph.condensation.minCommonAncestors
    --   #[{Nontrivial #0}] = #[#[Nontrivial #0]]`,
    -- * `ctx.minCommonAncestor? {NoZeroDivisors #0} ≈ ctx.graph.condensation.minCommonAncestors
    --   #[{NoZeroDivisors #0}] = #[#[NoZeroDivisors #0]]`,
    -- * `ctx.minCommonAncestor? {NoZeroDivisors (Polynomial #0)} ≈
    --   ctx.graph.condensation.minCommonAncestors #[{NoZeroDivisors (Polynomial #0), NoZeroDivisors
    --   #0}] = #[#[NoZeroDivisors #0]]` (`NoZeroDivisors (Polynomial #0)` is not a graph vertex).
    --
    -- Supposing that the above is the order in which the `for block in blocks` loop above processed
    -- these, its third iteration would, at this exact point, have `mcas = #[Nontrivial #0,
    -- NoZeroDivisors #0]` and `mca = NoZeroDivisors #0`, and so, without this `mcas.contains mca`
    -- check here, we'd add `mca` to `mcas` once more and produce `#[Nontrivial #0, NoZeroDivisors
    -- #0, NoZeroDivisors #0]`. Now, since all these are `Prop`-valued, the `sharesDataDesc` check
    -- below wouldn't flag this either, and so we'd propose the weakening candidate `[IsDomain R] ↝
    -- [Nontrivial R] [NoZeroDivisors R] [NoZeroDivisors R]`, which happens to pass verification and
    -- hence this weakening candidate would turn into a weakening _suggestion_ and be logged for the
    -- user. Now, the suggestion is technically perfectly valid, but the redundancy of the
    -- duplicated binder is glaring and certainly not desirable.
    --
    -- There were four such suggestions emitted over all of Mathlib in an older sweep that didn't
    -- have this check: `IsAlmostIntegral.coeff`,
    -- `Polynomial.eq_of_dvd_of_natDegree_le_of_leadingCoeff`,
    -- `WeierstrassCurve.Affine.irreducible_polynomial`, and `BoundedOrder.instSubsingleton`. (Note
    -- that this duplicate check is only one of several code changes that have been implemented
    -- since that sweep, so only removing this check here might not produce this exact same result.
    -- We are mostly just enumerating them here as a curiosity.)
    unless mcas.contains mca do mcas := mcas.push mca
  -- `partitionByDesc` partitioned the requirements, but that doesn't mean that the MCAs, which are
  -- "further up" than the requirements, couldn't have shared data descendants now. So we need to
  -- check. As always, this check is incomplete, due to our graph not encoding hyperedges.
  for i in [0:mcas.size] do
    for j in [i+1:mcas.size] do
      if ctx.sharesDataDesc mcas[i]! mcas[j]! then return none
  return some mcas


/--
Returns `true` iff `v.pattern` is made up of bvars, bvar-free expressions, and expressions that are
also entries of `b.pattern`.
-/
def MCAContext.reusesKeyArgsOf (_ctx : MCAContext) (b : TargetedBinder) (v : Vertex) : Bool :=
  v.pattern.all fun arg => arg.isBVar || !arg.hasLooseBVars || b.pattern.contains arg


/--
What might we replace `b` with, given that `b` requires (or, more accurately, uses) `reqVerts`?

This returns
* `some #[]` to indicate that `b` could be dropped altogether,
* `some #[mca]` to indicate that `b` could be replaced by `mca`,
* `some #[mca₁, …, mcaₙ]` to indicate that `b` could be split up into `mca₁`, …, `mcaₙ`, or
* `none` to indicate that `b` can't be weakened within `ctx.graph` under the constraints defined by
  `ctx.splitPolicy`, `ctx.absencePolicy`, and `ctx.includeSubsumers`.
-/
def MCAContext.replacement? (ctx : MCAContext) (b : TargetedBinder) (reqVerts : Array Vertex) :
    Option (Array Vertex) :=
  if reqVerts.isEmpty then some #[] else
  let singleClass? : Option Vertex :=
    (ctx.minCommonAncestor? b reqVerts).filter (ctx.strictlyStrongerThan b)
  match ctx.splitPolicy with
  | .forbid => singleClass?.map (#[·])
  | .allow =>
    match singleClass? with
    | some mca => some #[mca]
    | none => ctx.mcasPartition? b reqVerts
  | .prefer =>
    match ctx.mcasPartition? b reqVerts, singleClass? with
    | some mcas, some mca =>
      -- If any of the `mcaᵢ` is stronger than or equipotent to `mca`, then there's no point in
      -- splitting `b` up, so we just return `#[mca]` in that case.
      some (if mcas.all (fun mcaᵢ => ¬ ctx.reachesWitnessed mcaᵢ mca) then mcas else #[mca])
    | some mcas, none => some mcas
    | none, some mca => some #[mca]
    | none, none => none


/--
Return a (possibly empty) array of candidate weakenings for any of the targeted binders `binders`
such that the requirements `reqs` are still satisfied.
-/
public def mcaCandidates (graph : ClassGraph) (binders : Array TargetedBinder)
    (reqs : Array Requirement) (cfg : LinterConfig := {}) (includeSubsumers : Bool := true) :
    Array Candidate := Id.run do
  let ctx : MCAContext :=
    { graph, absencePolicy := cfg.absencePolicy, splitPolicy := cfg.splitPolicy, includeSubsumers }
  let mut out : Array Candidate := #[]
  for b in binders do
    let bReqVerts : HashSet Vertex := reqs.foldl (init := {}) fun bReqVerts' req =>
      if req.binder.id == b.id then bReqVerts'.insert req.toVertex else bReqVerts'
    let some mcas := ctx.replacement? b (ctx.filterReqVerts b bReqVerts) | continue
    -- Subsumption can sometimes lead to key args getting "modified": for example, `α` in the
    -- targeted binder becoming `αᵒᵖ` in the weakening candidate. Sometimes this can be genuinely
    -- desirable, but most of the time it's not, so, for the time being, we just try again with
    -- subsumption off if we are met with such a situation.
    let mcas :=
      if mcas.all (ctx.reusesKeyArgsOf b) then
        mcas
      else
        let ctxOff := { ctx with includeSubsumers := false }
        match ctxOff.replacement? b (ctxOff.filterReqVerts b bReqVerts) with
        | some alt => if alt.all (ctxOff.reusesKeyArgsOf b) then alt else mcas
        | none => mcas
    let shape := match mcas with
      | #[] => WeakeningShape.drop
      | #[mca] => WeakeningShape.weaken mca
      | mcas => WeakeningShape.split mcas
    out := out.push { binder := b, shape }
  return out
