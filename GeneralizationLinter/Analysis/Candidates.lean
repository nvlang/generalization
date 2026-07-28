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

/-- The kinds of possible weakening suggestions. -/
public inductive WeakeningShape where
  /-- Binder is entirely unused, and can therefore be dropped (removed). -/
  | drop
  /-- Binder can be weakened to `weakerVertex`. -/
  | weaken (weakerVertex : Vertex)
  /-- Binder can be weakened by splitting it up into `weakerVertices`. -/
  | split (weakerVertices : Array Vertex)
deriving Inhabited


/-- An unverified weakening proposal. -/
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
Things that we need to compute the least upper bounds, or things which may affect said computation,
compiled into one structure.
-/
private structure LUBContext where
  /-- Class graph. -/
  graph : ClassGraph
  /-- See `AbsencePolicy`. -/
  absencePolicy : AbsencePolicy
  /-- See `SplitPolicy`. -/
  splitPolicy : SplitPolicy
  /-- Subsumption in vertex matching. -/
  includeSubsumers : Bool


/-- Returns `true` iff `u` reaches `v` in `ctx.graph`. -/
def LUBContext.reachesV (ctx : LUBContext) (u v : Vertex) : Bool :=
  (u.matchingVertices ctx.includeSubsumers).any fun u' =>
    (v.matchingVertices ctx.includeSubsumers).any fun v' => ctx.graph.condensation.reaches u' v'

/--
Returns `true` iff `u` and `v` can be unified.

**Note:** We use syntactic equality in this process, so e.g. `OrderDual ℕ` does not unify with `ℕ`
according to us, even though Lean's actual unification mechanism _would_ unify them, since it uses
definitional equality.
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
    -- In patterns, we just support bvars, applications, and constants, and constants never contain
    -- bvars, so if we reach this point we know that the expression doesn't contain any bvar at all.
    | _ => false
  /-- Given constraints `σ` mapping bvar indices to `Expr` values they are required to have, see if
      two expressions can be unified, and return the updated constraints map if so. -/
  unifyPatterns (σ : HashMap Nat Expr) : Expr → Expr → Option (HashMap Nat Expr)
    | .bvar i, e
    | e, .bvar i =>
      -- Examples: `.bvar 0, .bvar 1`, `ℕ, .bvar 1`, etc.
      match σ[i]? with -- Is `.bvar i` constrained?
      -- Yes ⟹ Unfold `.bvar i` to whatever its constrained to and check `e` against that.
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
    -- A constant can be unified with an expression iff the latter is equal to the former. Since we
    -- only support bvars, applications, and constants in patterns, we know that at least one of `a`
    -- or `b` has to be a constant at this point, so `a` and `b` are unifiable iff they're equal.
    -- Note that we use syntactic equality, so e.g. `OrderDual ℕ` does not unify with `ℕ` according
    -- to us, even though Lean's actual unification mechanism _would_ unify them, since it uses
    -- definitional equality.
    | a, b => if a == b then some σ else none


/-- Return the data descendants of `v` in `ctx.graph` as an array `Array Vertex`. -/
def LUBContext.dataDescendants (ctx : LUBContext) (v : Vertex) : Array Vertex :=
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
Workshop on Formal Mathematics for Mathematicians, April 19, 2023. CEUR Workshop Proceedings.
Retrieved from [https://ceur-ws.org/Vol-3377/fmm12.pdf](https://ceur-ws.org/Vol-3377/fmm12.pdf).


---
**Examples**

* `sharesDataDesc` would return `true` for `Semigroup` and `MulOneClass`, since those two classes
  share the data-carrying descendant `Mul`. This means that a theorem with hypothesis `[Monoid α]`
  but which uses only `[Semigroup α]` and `[MulOneClass α]` can nonetheless not split the `Monoid`
  hypothesis up, because the instances of `Mul` that `Semigroup` and `MulOneClass` each use would
  not guaranteed to be the same anymore.
* `sharesDataDesc` would return `false` for `IsPreorder` and `Std.Total`, since those two classes
  only share the non-data-carrying descendants such as `Std.Refl`. This means that a theorem with
  hypothesis `[IsLinearOrder r]` but which uses only `[IsPreorder r]` and `[Std.Total r]` could
  safely split the `IsLinearOrder` hypothesis up, because the instances of `Std.Refl` that
  `IsPreorder` and `Std.Total` each use are guaranteed to be equal due to proof irrelevance.
-/
def LUBContext.sharesDataDesc (ctx : LUBContext) (u v : Vertex) : Bool :=
  (u.matchingVertices ctx.includeSubsumers).any fun u' =>
    let descsᵤ := ctx.dataDescendants u'
    (v.matchingVertices ctx.includeSubsumers).any fun v' =>
      let descsᵥ := ctx.dataDescendants v'
      descsᵤ.any fun dᵤ => descsᵥ.any (Vertex.unifiable dᵤ ·)

/--
Applies two filters to `reqVerts` and returns the result. The filters are:
* Every bvar of a requirement's `pattern` must be substitutable by the binder's carriers.
* Requirements that are descendants of other requirements are redundant and hence dropped.
-/
def LUBContext.filterReqVerts (ctx : LUBContext) (b : TargetedBinder)
    (reqVerts : HashSet Vertex) : Array Vertex :=
  let byArity := reqVerts.toArray.filter (fun v => v.pattern.all (·.looseBVarRange ≤ b.subst.size))
  byArity.filter fun u =>
    ¬ byArity.any fun v => v != u && ctx.reachesV v u && ¬ ctx.reachesV u v


/--
These are class names that Mathlib has access to but which, if found within an SCC, have preferred
alternatives.
-/
def sccDemotedHeads : List Name := [`NSMul, `ZSMul, `NPow, `ZPow, `OfNat, `Trans]

/--
Deterministically picks a vertex within a given SCC, avoiding any vertex whose `Vertex.name` is in
`sccDemotedHeads`.
-/
def sccRepresentative (scc : Array Vertex) : Option Vertex :=
  let pick (vertices : Array Vertex) : Option Vertex := vertices.foldl (init := none) fun best v =>
    match best with
    | none => some v
    | some w => if (v.name.cmp w.name).isLT then some v else some w
  pick (scc.filter fun v => !sccDemotedHeads.contains v.name) <|> pick scc


/--
Returns the least upper bound (LUB) of `reqs` in `ctx.graph.condensation`, if a unique LUB exists.
Otherwise, returns `none`.
-/
def LUBContext.lub (ctx : LUBContext) (b : TargetedBinder) (reqs : Array Vertex) :
    Option Vertex :=
  -- De-duplicate, and include vertices that match requirements too if `includeSubsumers` is `true`,
  -- converting `reqs` into an array of sets, which will be interpreted by `minCommonAncestors` as
  -- an AND of ORs to satisfy.
  let reqs := reqs.map (fun req => HashSet.ofArray (req.matchingVertices ctx.includeSubsumers))
  let mca := (ctx.graph.condensation.minCommonAncestors reqs ctx.absencePolicy).filter fun scc =>
    scc[0]?.any (ctx.reachesV b.toVertex ·)
  match mca with
  | #[scc] => sccRepresentative scc
  | _ => none -- `mca` is empty or has size ≥2
  -- #TODO (low priority): If `mca` has size ≥2, it means there's multiple incomparable minimal
  -- common ancestors, each of which single-handedly satisfies all requirements (see
  -- `minCommonAncestors`'s docstring for an example). Instead of dropping them all and pretending
  -- there's no possible weakenings, we could try to simply present them as multiple viable options
  -- (after verifying them, of course), or even just pick one ancestor from `mca` according to some
  -- deterministic procedure and just go with that. However, this shouldn't happen all that often,
  -- so it should be considered a low-priority opportunity for future work.

/-- Is `v` strictly weaker than `b` according to `ctx.graph`? -/
def LUBContext.strictlyWeaker (ctx : LUBContext) (b : TargetedBinder) (v : Vertex) :
    Bool :=
  let bVertex := b.toVertex
  v != bVertex && ctx.reachesV bVertex v && ¬ ctx.reachesV v bVertex


/--
Partition `reqs` into non-data-descendant-sharing blocks and return the LUBs of the blocks as an
array, or `none` if `reqs` can't be split up, or if any of the blocks don't have a LUB, or if any of
the blocks' LUBs are not strictly weaker than `b` (in which case we'd be e.g. replacing `[Group G]`
with `[Group G] […]`, which would be pointless).
-/
def LUBContext.lubsPartition (ctx : LUBContext) (b : TargetedBinder) (reqs : Array Vertex) :
    Option (Array Vertex) := Id.run do
  let blocks := partitionByDesc (HashSet.ofArray reqs) ctx.sharesDataDesc
  if blocks.size ≤ 1 then return none -- If `reqs` can't be split up, return `none`.
  let mut lubs : Array Vertex := #[]
  for block in blocks do
    let some lub := ctx.lub b block.toArray | return none
    unless ctx.strictlyWeaker b lub do return none
    lubs := lubs.push lub
  return some lubs


/--
What might we replace `b` with, given that `b` requires (or, more accurately, uses) `reqVerts`?

This returns
* `some #[lub]` to indicate that `b` could be replaced by `lub`,
* `some #[lub₁, …, lubₙ]` to indicate that `b` could be split up into `lub₁`, …, `lubₙ`, or
* `none` to indicate that `b` can't be weakened within `ctx.graph` under the constraints defined by
  `ctx.splitPolicy`, `ctx.absencePolicy`, and `ctx.includeSubsumers`.
-/
def LUBContext.replacement? (ctx : LUBContext) (b : TargetedBinder) (reqVerts : Array Vertex) :
    Option (Array Vertex) :=
  if reqVerts.isEmpty then some #[] else
  let singleClass? : Option Vertex := (ctx.lub b reqVerts).filter (ctx.strictlyWeaker b)
  match ctx.splitPolicy with
  | .forbid => singleClass?.map (#[·])
  | .allow =>
    match singleClass? with
    | some lub => some #[lub]
    | none => ctx.lubsPartition b reqVerts
  | .prefer =>
    match ctx.lubsPartition b reqVerts, singleClass? with
    | some lubs, some lub =>
      -- If any of the `lubᵢ` is stronger than or equipotent to `lub`, then there's no point in
      -- splitting `b` up, so we just return `#[lub]` in that case.
      some (if lubs.all (fun lubᵢ => ¬ ctx.reachesV lubᵢ lub) then lubs else #[lub])
    | some lubs, none => some lubs
    | none, some lub => some #[lub]
    | none, none => none


/--
Return a (possibly empty) array of candidate weakenings for any of the targeted binders `binders`
such that the requirements `reqs` are still satisfied.
-/
public def lubCandidates (graph : ClassGraph) (binders : Array TargetedBinder)
    (reqs : Array Requirement) (cfg : LinterConfig := {}) (includeSubsumers : Bool := true) :
    Array Candidate := Id.run do
  let ctx : LUBContext :=
    { graph, absencePolicy := cfg.absencePolicy, splitPolicy := cfg.splitPolicy, includeSubsumers }
  let mut out : Array Candidate := #[]
  for b in binders do
    let bReqVerts : HashSet Vertex := reqs.foldl (init := {}) fun bReqVerts' req =>
      if req.binder.fvar == b.fvar then bReqVerts'.insert req.toVertex else bReqVerts'
    let some lubs := ctx.replacement? b (ctx.filterReqVerts b bReqVerts) | continue
    let shape := match lubs with
      | #[] => WeakeningShape.drop
      | #[lub] => WeakeningShape.weaken lub
      | lubs => WeakeningShape.split lubs
    out := out.push { binder := b, shape }
  return out
