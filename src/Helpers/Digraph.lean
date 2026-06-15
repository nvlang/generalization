/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
module

public import Std.Data.HashMap

namespace GeneralizationLinter

/-!
TODO: Module docstring.
-/

open Std

/--
Directed graph with vertices of type V, implemented through an adjacency list
`adj`.
-/
public structure Digraph (V : Type) [BEq V] [Hashable V] where
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

variable {V : Type} [BEq V] [Hashable V]

/--
**Warning:** If called with a vertex that is not in `G`, this will silently
return the empty array.
-/
public def succs (G : Digraph V) (v : V) : Array V :=
  G.adj.getD v #[]

public def insertVertex (G : Digraph V) (v : V) : Digraph V :=
  if G.adj.contains v then G else ⟨G.adj.insert v #[]⟩

/--
Here, `s` stands for "source vertex" and `t` stands for "target vertex" of the
edge to be inserted.
-/
public def insertEdge (G : Digraph V) (s : V) (t : V) : Digraph V :=
  let G := (G.insertVertex s).insertVertex t
  let existingSuccs := G.succs s
  if existingSuccs.contains t then G else ⟨G.adj.insert s (existingSuccs.push t)⟩
