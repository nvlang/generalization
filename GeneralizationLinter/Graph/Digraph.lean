/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
module

public import Std.Data.HashMap.Basic
public import Std.Data.HashSet.Basic

namespace GeneralizationLinter

/-!
# Directed Graphs

Small directed graph module providing the core graph-theoretic mechanisms used
by the generalization linter.

---
**Main definitions**

* `Digraph`: Implemented as an adjacency list.
* `Condensation`: Condensation of digraph into DAG of SCCs.
* `minCommonAncestors`: Find the least upper bounds.

---
**References**

* [A. J. Best. 2023. _Automatically Generalizing Theorems Using
  Typeclasses_.][best2023automaticallyGeneralizingTheorems]
* [D. J. King, J. Launchbury. 1995. _Structuring depth-first search algorithms
  in Haskell_.][10.1145/199448.199530]

-/

open Std (HashMap HashSet)

/--
Directed graph with vertices of type V, implemented through an adjacency list
`adj`.
-/
public structure Digraph (V : Type u) [BEq V] [Hashable V] where
  /--
  Adjacency list of the directed graph.

  Given a vertex `a`, `adj[a]` is the array of immediate successors of `a`.

  **Default:** `{}`

  ---
  **Example**

  ```
  1 → 2 ─┐
  ↓   ↑  │    5
  3   4 ←┘
  ```

  For the graph shown above (where the `5` is an isolated vertex), we'd have:
  * `adj[1] = [2, 3]`
  * `adj[2] = [4]`
  * `adj[3] = []`
  * `adj[4] = [2]`
  * `adj[5] = []`

  ---
  **Implementation Notes**

  Storing the successors as an `Array` instead of a `List` is more efficient for
  our purposes. Conceptually, either one would work.
  -/
  adj : HashMap V (Array V) := {}
deriving Inhabited

variable {V : Type u} [BEq V] [Hashable V]

namespace Digraph


/-- Returns an array of the vertices of `G` in some order. -/
public def vertices (G : Digraph V) : Array V := G.adj.keysArray


/-- Returns `true` iff `G` contains the vertex `v`. -/
public def contains (G : Digraph V) (v : V) : Bool := G.adj.contains v


/--
Returns the immediate successors of `v` in `G`.

**Warning:** If `v` is not in `G`, this will silently return the empty array.
-/
public def succs (G : Digraph V) (v : V) : Array V :=
  G.adj.getD v #[]

/-- Inserts vertex `v` into `G`, and returns updated `G`. -/
public def insertVertex (G : Digraph V) (v : V) : Digraph V :=
  if G.contains v then G else ⟨G.adj.insert v #[]⟩

/--
Inserts edge `s → t` into `G`, and returns updated `G`. (`s` stands for "source
vertex" and `t` stands for "target vertex" of the edge to be inserted.)
-/
public def insertEdge (G : Digraph V) (s : V) (t : V) : Digraph V :=
  let G := (G.insertVertex s).insertVertex t
  let existingSuccs := G.succs s
  if existingSuccs.contains t then G else ⟨G.adj.insert s (existingSuccs.push t)⟩

/-! ### Reachability -/

/--
Depth-first search to compute transitive closure of `v` under `G`.

* `acc` is an array that will eventually contain all vertices reachable from
  `v`, including `v` itself. If `G` is acyclic, this list will be returned in
  postorder.
* `vis` is the set of visited vertices. It will eventually also contain all
  vertices reachable from `v`, including `v` itself.
-/
public partial def dfs (G : Digraph V) (v : V) (acc : Array V) (vis : HashSet V) :
    Array V × HashSet V :=
  if vis.contains v then (acc, vis)
  else
    let vis := vis.insert v -- "visited v"
    let (acc, vis) := (G.succs v).foldl (init := (acc, vis)) fun (acc, vis) w => G.dfs w acc vis
    (acc.push v, vis)

/-- Returns the set of vertices of `G` reachable from `v`. -/
public def downSet (G : Digraph V) (v : V) : HashSet V := (G.dfs v #[] {}).2


/-- Returns map from vertices to the set of vertices that each can reach. -/
public def downSets (G : Digraph V) : HashMap V (HashSet V) :=
  G.adj.fold (init := {}) fun sets v _ => sets.insert v (G.downSet v)

public def postorder (G : Digraph V) : Array V :=
  (G.vertices.foldl (init := (#[], {})) fun (acc, vis) v => G.dfs v acc vis).1


/-- Returns [transpose](https://en.wikipedia.org/wiki/Transpose_graph) of `G`. -/
public def transpose (G : Digraph V) : Digraph V :=
  G.adj.fold (init := {}) fun G' s ts =>
    ts.foldl (init := G'.insertVertex s) fun G'' t => G''.insertEdge t s


/-! ## Condensation -/

/--
Strongly-connected components of `G`, computed with [Kosaraju–Sharir's
algorithm](https://en.wikipedia.org/wiki/Kosaraju%27s_algorithm).
-/
public def sccs (G : Digraph V) : Array (Array V) :=
  let G' := G.transpose
  (
    G.postorder.reverse.foldl (init := (({} : HashSet V), #[]))
      fun (vis, comps) v =>
        if vis.contains v then (vis, comps)
        else
          let (comp, vis) := G'.dfs v #[] vis
          (vis, comps.push comp)
  ).2


public structure Condensation (V : Type u) [BEq V] [Hashable V] where
  /-- Digraph of indices. Guaranteed to be a DAG. -/
  graph : Digraph Nat
  /-- Maps an index to the array of vertices contained in the SCC corresponding to the index. -/
  members : HashMap Nat (Array V)
  /-- Maps a vertex to the index of its parent SCC. -/
  componentsMap : HashMap V Nat
  /-- Maps an index to its corresponding down-set. -/
  downSetsByIndex : HashMap Nat (HashSet Nat)
  /-- `graph.vertices`, cached inside `condense`. -/
  vertices : Array Nat


/--
Condense digraph `G` into DAG of SCCs of `G` and return the result as a
`Condensation` structure.
-/
public def condense (G : Digraph V) : Condensation V :=
  let (members, componentsMap) := G.sccs.foldl
    (init := (({} : HashMap Nat (Array V)), ({} : HashMap V Nat)))
    fun (members', componentsMap') comp =>
      let idx := members'.size
      (
        members'.insert idx comp,
        comp.foldl (init := componentsMap') fun componentsMap' v => componentsMap'.insert v idx
      )
  let graph : Digraph Nat := G.adj.fold (init := ({} : Digraph Nat)) fun graph' s ts =>
    let idx_s := componentsMap.getD s 0 -- idx_s is the index of the SCC containing vertex s
    ts.foldl (init := graph'.insertVertex idx_s) fun graph'' t =>
      let idx_t := componentsMap.getD t 0
      if idx_s == idx_t then graph'' else graph''.insertEdge idx_s idx_t
  { graph, members, componentsMap, downSetsByIndex := graph.downSets, vertices := graph.vertices }


namespace Condensation

/-- Returns indices of SCCs containing the vertices `vs`. -/
public def indicesOf (c : Condensation V) (vs : HashSet V) : HashSet Nat :=
  vs.fold (init := {}) fun indices v => match c.componentsMap[v]? with
    | some idx => indices.insert idx
    | none     => indices

/-! ### Least Upper Bounds -/

/--
Establishes how `minCommonAncestors` should handle inputs that are unexpectedly
not vertices of the given condensation.
-/
public inductive AbsencePolicy
  /-- Return an empty array. (Default.) -/
  | failClosed
  /-- Filter out bad inputs and proceed as usual. -/
  | failOpenGuarded
deriving BEq, Repr


/--
**Idea:** Given the set of classes that a theorem uses, find the minimal common ancestor of that set
in the class DAG, i.e., the weakest common ancestor of the elements of the set (i.e., their _join_),
if a unique one exists. The class DAG is not a lattice, however, so the join is not guaranteed to
exist. In those cases, an antichain of incomparable answers is returned.

---
**Implementation notes**

The set of used classes is given as an array (`requirements`) of smaller sets. Currently, these
smaller sets are usually singletons, except for used classes that are not universe polymorphic. In
those cases, the corresponding smaller set consists of the used class with the specific universe
level, and the universe-polymorphic version of the used class.

The idea is that the array of smaller sets communicates the requirements as a general _AND of ORs._
Let's call each smaller set a set of _witnesses_. The question then becomes:

> Find a class that is a common ancestor to at least one witness of each requirement (i.e., a common
ancestor of at least one transversal of the sets of witnesses).

The answer is returned as an array of arrays. Any element of any of the inner arrays is a class
which satisfies, on its own, all the given requirements. The structure within which the classes are
given encodes the relationships between all of these classes:

* All classes within each inner array are mutually equipotent. Each inner array therefore represents
  a single SCC of the class graph pre-condensation (or, equivalently, a single vertex in the class
  _DAG_, i.e., in the condensation of the class graph).
* The SCCs listed in the outer array are pairwise unreachable in the class graph. Alternatively,
  roughly speaking, the outer array represents the _antichain_ of vertices of the class DAG which
  satisfy the requirements. More precisely, each of these vertices is a bona-fide minimal common
  ancestor; it's just that minimality doesn't generally imply uniqueness in our case, since the
  class DAG is not a lattice.

---
**Examples**

* **Unique minimal common ancestor:** Sometimes, there is exactly one minimal common ancestor.

  ```
  minCommonAncestors #[{Monoid}, {CommSemigroup}] = #[#[CommMonoid]]
  ```

* **No common ancestors:** Quite often, there may not exist any class which satisfies all the given
  requirements.

  ```
  minCommonAncestors #[{Inv}, {SDiff}] = #[]
  ```

* **Minimal common ancestors of single classes:** Within an SCC of the class graph
  (pre-condensation), all classes are pairwise equipotent. This means that any element of the SCC is
  a minimal common ancestor of any other element or subset of the SCC. Note that the vast majority
  of the SCCs of the class graph (pre-condensation) are singletons.

  ```
  minCommonAncestors #[{Nonempty}] = #[#[Inhabited, Nonempty]]
  minCommonAncestors #[{Monoid}] = #[#[Monoid]]
  ```

* **Multiple non-equipotent minimal common ancestors:** Rarely, requirements may have multiple
  non-equipotent minimal common ancestors.

  ```
  minCommonAncestors #[{Add}, {Mul}] = #[
    #[FirstOrder.Language.Structure]
    #[Lean.Grind.Semiring],
    #[Distrib],
  ]
  ```
-/
public def minCommonAncestors (c : Condensation V) (reqs : Array (HashSet V))
    (ap : AbsencePolicy := .failClosed) : Array (Array V) :=
  -- map sets of required classes to sets of (the indices of) required SCCs
  let reqs := reqs.map c.indicesOf
  let reqs := match ap with
    | .failClosed => if reqs.any (·.isEmpty) then #[] else reqs
    | .failOpenGuarded => reqs.filter (!·.isEmpty)
  if reqs.isEmpty then #[]
  else
    let reqArr : Array (Array Nat) := reqs.map (·.toArray)
    -- common ancestors are vertices which satisfy all the requirements
    let commonAncestors := c.vertices.filter fun i =>
      let d := c.downSetsByIndex.getD i {}
      reqArr.all fun req => req.any d.contains
    -- filter out non-minimal common ancestors
    let minimal := commonAncestors.filter fun ca =>
      let d := c.downSetsByIndex.getD ca {}
      -- there isn't (`¬`) any other (`ca' != ca`) common ancestor weaker than `ca`
      -- (`d.contains ca'`)
      ¬ commonAncestors.any fun ca' => ca' != ca && d.contains ca'
    -- convert each SCC index to the array of its members
    minimal.map fun ca => c.members.getD ca #[]


/--
Given the condensation of a graph and two vertices `s` and `t` of the graph
(pre-condensation), returns whether `s` reaches `t` in the graph
(pre-condensation).
-/
public def reaches (c : Condensation V) (s t : V) : Bool :=
  match c.componentsMap[s]?, c.componentsMap[t]? with
  | some s_idx, some t_idx => (c.downSetsByIndex.getD s_idx {}).contains t_idx
  | _, _ => false


/--
Given an array `xs` and methods

* `fuse` to merge two elements of the array and
* `connected` to query whether two elements of the array should be merged,

returns an array in which no two elements should be merged anymore.

We require the following preconditions:

* `connected` must be a symmetric relation.
* For any `a b c : α`, `connected a c` implies `connected (fuse a b) c`.

---
**Examples:**

```
coalesceWith (·.append ·) (fun x y : List Nat => x.any y.contains)
  #[[1], [1, 2], [3], [2, 4], [5, 6]] = #[[1, 1, 2, 2, 4], [3], [5, 6]]
coalesceWith (·.union ·) (fun x y : HashSet Nat => !(x.inter y).isEmpty)
  #[{1}, {1, 2}, {3}, {2, 4}, {5, 6}] = #[{1, 2, 4}, {3}, {5, 6}]
```
-/
public def coalesceWith {α : Type _} [Inhabited α] (fuse : α → α → α) (connected : α → α → Bool)
    (xs : Array α) : Array α :=
  let rec loop (xs : Array α) (fuel : Nat) : Array α :=
    match fuel with
    | 0 => xs
    | fuel + 1 =>
      let fused : Option (Array α) := Id.run do
        for i in [0:xs.size] do
          for j in [i+1:xs.size] do
            if connected xs[i]! xs[j]! then
              return some (
                #[fuse xs[i]! xs[j]!] ++ ((xs.eraseIdxIfInBounds j).eraseIdxIfInBounds i)
              )
        return none
      match fused with
      | none => xs
      | some xs' => loop xs' fuel
  loop xs (xs.size * xs.size + 1)


/--
Partitions `used` into subsets whose down-sets are disconnected according to `conn`.

---
**Example**

Roughly speaking, in our use-case, if `partitionByDesc` was called on `{Semigroup, MulOneClass,
IsPreorder, IsTotal}`, it would return `[{Semigroup, MulOneClass}, {IsPreorder}, {IsTotal}]`. Refer
to the examples documented for `sharesDataDesc` for more information.
-/
public def partitionByDesc (used : HashSet V) (conn : V → V → Bool) : Array (HashSet V) :=
  coalesceWith (·.union ·) (fun a b => a.any fun x => b.any (conn x))
    (used.toArray.map fun v => {v})
