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
TODO: Module docstring.

References:
* hackage-content.haskell.org/package/containers-0.8/docs/src/Data.Graph.html
-/

open Std

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
  ### Example

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
  ### Implementation Notes

  Storing the successors as an `Array` instead of a `List` is more efficient for
  our purposes. Conceptually, either one would work.
  -/
  adj : HashMap V (Array V) := {}
  deriving Inhabited

namespace Digraph

variable {V : Type u} [BEq V] [Hashable V]

public def vertices (G : Digraph V) : Array V := G.adj.keysArray

public def contains (G : Digraph V) (v : V) : Bool := G.adj.contains v

/--
**Warning:** If called with a vertex that is not in `G`, this will silently
return the empty array.
-/
public def succs (G : Digraph V) (v : V) : Array V :=
  G.adj.getD v #[]

public def insertVertex (G : Digraph V) (v : V) : Digraph V :=
  if G.contains v then G else ⟨G.adj.insert v #[]⟩

/--
Here, `s` stands for "source vertex" and `t` stands for "target vertex" of the
edge to be inserted.
-/
public def insertEdge (G : Digraph V) (s : V) (t : V) : Digraph V :=
  let G := (G.insertVertex s).insertVertex t
  let existingSuccs := G.succs s
  if existingSuccs.contains t then G else ⟨G.adj.insert s (existingSuccs.push t)⟩

/--
Depth-first search to compute transitive closure of `v` under `G`.

**Note:** If `G` is acyclic, then the list that this returns will be
topologically sorted.
* `acc` is an array that will eventually contain all vertices reachable from `v`,
  including `v` itself, in postorder.
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

/-- Return the set of vertices of `G` reachable from `v`. -/
public def downSet (G : Digraph V) (v : V) : HashSet V := (G.dfs v #[] {}).2

/-- Return map from vertices to the set of vertices that each can reach. -/
public def downSets (G : Digraph V) : HashMap V (HashSet V) :=
  G.adj.fold (init := {}) fun sets v _ => sets.insert v (G.downSet v)

public def postorder (G : Digraph V) : Array V :=
  (G.vertices.foldl (init := (#[], {})) fun (acc, vis) v => G.dfs v acc vis).1

/-- Transpose of `G`. See also: https://en.wikipedia.org/wiki/Transpose_graph -/
public def transpose (G : Digraph V) : Digraph V :=
  G.adj.fold (init := {}) fun G' s ts =>
    ts.foldl (init := G'.insertVertex s) fun G'' t => G''.insertEdge t s

/--
Strongly-connected components of `G`, computed with Kosaraju–Sharir's algorithm.

See also: https://en.wikipedia.org/wiki/Kosaraju%27s_algorithm
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
  componentOf : HashMap V Nat

/-- Condense digraph `G` into DAG of SCCs of `G`, returned as a `Condensation` structure. -/
public def condense (G : Digraph V) : Condensation V :=
  let (members, componentOf) := G.sccs.foldl
    (init := (({} : HashMap Nat (Array V)), ({} : HashMap V Nat)))
    fun (members', componentOf') comp =>
      let idx := members'.size
      (
        members'.insert idx comp,
        comp.foldl (init := componentOf') fun componentOf' v => componentOf'.insert v idx
      )
  let graph : Digraph Nat := G.adj.fold (init := ({} : Digraph Nat)) fun graph' s ts =>
    let idx_s := componentOf.getD s 0 -- idx_s is the index of the SCC containing vertex s
    ts.foldl (init := graph'.insertVertex idx_s) fun graph'' t =>
      let idx_t := componentOf.getD t 0
      if idx_s == idx_t then graph'' else graph''.insertEdge idx_s idx_t
  { graph, members, componentOf }

/-- Indices of SCCs containing the vertices `vs`. -/
public def indicesOf (c : Condensation V) (vs : HashSet V) : HashSet Nat :=
  vs.fold (init := {}) fun indices v => match c.componentOf[v]? with
    | some idx => indices.insert idx
    | none     => indices

/--
Compute the meet of the vertices in `query`.

Note: To avoid duplication of work, `down_sets` should be precomputed once,
before ever calling `meet`, and then passed to all subsequent calls of `meet`.
-/
public def meet (c : Condensation V)
    (down_sets : HashMap Nat (HashSet Nat))
    (query : HashSet V) : Array Nat :=
  if query.size == 0 || !query.all (c.componentOf.contains ·) then #[]
  else
    let query_indices := indicesOf c query
    -- keep vertex v iff `query_indices ⊆ down_set_of_v`
    let common_ancestors := c.graph.vertices.filter fun v =>
      let down_set := down_sets.getD v {}
      query_indices.all fun idx => down_set.contains idx
    -- keep vertex v iff (common_ancestors ∩ down_set_of_v = {v})
    common_ancestors.filter fun v =>
      let down_set := down_sets.getD v {}
      ¬ common_ancestors.any fun v' =>
        v' != v && down_set.contains v'
