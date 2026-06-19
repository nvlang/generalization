/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
import GeneralizationLinter.Helpers.Digraph

/-!
# Unit tests: the generic directed graph (`Digraph`)

Tests the real adjacency-list API in `GeneralizationLinter/Helpers/Digraph.lean`
(`insertVertex` / `insertEdge` / `succs` / `contains`), plus the two structural ops the
weakening pipeline depends on and that the audits flagged for regression coverage:
`transpose` (must REVERSE edges — a one-character bug here silently corrupts `sccs`/
`condense`/the meet) and `condense` (a cycle must collapse to a single SCC).

This file targets *implemented* code, so it goes green as soon as the library builds.

The greatest-lower-bound **meet** the linter relies on is the GENERIC
`Condensation.minimalCommonAncestors` (v4; renamed from `meet`, now witness-set based and
fail-closed). Its edge cases — witness-set disjunction, fail-closed on an absent vertex,
a diamond's unique GLB, and an incomparable-parents antichain — are unit-tested in
`tests/Unit/Condensation.lean`, and pinned *behaviorally* by `P3`/`S2` in
`tests/Behavior/Weakening.lean`.
-/

open GeneralizationLinter

/-- The graph from `Digraph`'s own docstring: `1→2`, `1→3`, `2→4`, `4→2`, isolated `5`. -/
def g : Digraph Nat :=
  (((({} : Digraph Nat).insertEdge 1 2).insertEdge 1 3).insertEdge 2 4 |>.insertEdge 4 2).insertVertex 5

#guard g.contains 1
#guard g.contains 5
#guard ! g.contains 9
#guard g.succs 1 == #[2, 3]
#guard g.succs 2 == #[4]
#guard g.succs 3 == #[]
#guard g.succs 4 == #[2]
#guard g.succs 5 == #[]

-- invariants the class-DAG construction relies on:
#guard (g.insertEdge 1 2).succs 1 == #[2, 3]   -- a duplicate edge is a no-op
#guard (g.insertVertex 1).succs 1 == #[2, 3]   -- re-inserting an existing vertex keeps its edges

/-! ## `transpose` regression — must REVERSE edges (guards the `insertEdge t s` direction) -/

def line : Digraph Nat := (({} : Digraph Nat).insertEdge 1 2)
#guard line.transpose.succs 2 == #[1]   -- the edge 1→2 becomes 2→1
#guard line.transpose.succs 1 == #[]    -- …and nothing points the original way
#guard line.transpose.contains 1        -- vertices are preserved

/-! ## `condense` regression — a cycle collapses to ONE component; acyclic stays apart -/

-- a 2-cycle 1⇄2 is one strongly-connected component
def twoCycle : Digraph Nat := (({} : Digraph Nat).insertEdge 1 2).insertEdge 2 1
#guard twoCycle.condense.members.size == 1

-- an acyclic chain 1→2→3 is three singleton components
def chain : Digraph Nat := (({} : Digraph Nat).insertEdge 1 2).insertEdge 2 3
#guard chain.condense.members.size == 3
