/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
import GeneralizationLinter.Helpers.Digraph

/-!
# Unit tests: the meet on the condensation (`minimalCommonAncestors` / `commonAncestorBlocks`)

These pin the v4 generic meet (renamed from `meet`). Edges point STRONGER → WEAKER
(`u → v` means "`u` provides `v`"), so `↓v` is everything `v` provides, and a *common
ancestor* of a query is a vertex providing every query element. The meet is the minimal
(weakest) such antichain.

TDD STATUS: these target the v4 API (`Condensation.minimalCommonAncestors` taking per-element
WITNESS SETS and returning `Array (Array V)`; `Condensation.commonAncestorBlocks`), so they
are RED until that lands — but each expected value is justified below.

Helper: flatten the antichain-of-SCCs to its vertices and sort, since here every SCC is a
singleton (the graphs are acyclic) and order is irrelevant.
-/

open GeneralizationLinter

private def flatSorted (xss : Array (Array Nat)) : Array Nat :=
  xss.flatten.qsort (· < ·)

/-! ## Witness-set DISJUNCTION (the v2 recall bug: must NOT collapse OR into AND)

Graph: `10→1, 10→2, 20→1, 20→3`. With witnesses `#[{1}, {2,3}]`, an ancestor must reach `1`
AND (reach `2` OR `3`). Both `10` (via `2`) and `20` (via `3`) qualify — a 2-class split.
If the witness sets were wrongly FLATTENED to `{1,2,3}` (one conjunctive element), an
ancestor would need to reach `1` AND `2` AND `3` — neither `10` nor `20` does, so the result
would be empty. So this graph distinguishes the correct OR from the buggy AND. -/
def gOr : Digraph Nat := (((({} : Digraph Nat).insertEdge 10 1).insertEdge 10 2).insertEdge 20 1).insertEdge 20 3

#guard flatSorted (gOr.condense.minimalCommonAncestors #[{1}, {2, 3}]) == #[10, 20]
-- the flattened (buggy) query would yield nothing — pinned here as a guard against regressing:
#guard gOr.condense.minimalCommonAncestors #[{1, 2, 3}] == #[]

/-! ## Diamond → unique GLB

Graph: `1→2, 1→3, 2→4, 3→4`. A binder used for both `2` and `3` (incomparable) has a unique
weakest common provider, the apex `1`. -/
def gDiamond : Digraph Nat := (((({} : Digraph Nat).insertEdge 1 2).insertEdge 1 3).insertEdge 2 4).insertEdge 3 4

#guard flatSorted (gDiamond.condense.minimalCommonAncestors #[{2}, {3}]) == #[1]

/-! ## Incomparable parents → a 2-class antichain

Graph: `100→1, 100→2, 200→1, 200→2`. Two incomparable vertices each provide both `1` and `2`,
so the meet is the antichain `{100, 200}` (the shape that becomes a split suggestion). -/
def gAnti : Digraph Nat := (((({} : Digraph Nat).insertEdge 100 1).insertEdge 100 2).insertEdge 200 1).insertEdge 200 2

#guard flatSorted (gAnti.condense.minimalCommonAncestors #[{1}, {2}]) == #[100, 200]

/-! ## Fail-closed vs fail-open-guarded on an ABSENT query vertex (Q3)

`99` is not in `gDiamond`. `failClosed` (default) ⇒ the whole query yields `#[]`;
`failOpenGuarded` ⇒ drop the absent element and meet over the rest (here `{2}` ⇒ `2`). -/
#guard gDiamond.condense.minimalCommonAncestors #[{2}, {99}] .failClosed == #[]
#guard flatSorted (gDiamond.condense.minimalCommonAncestors #[{2}, {99}] .failOpenGuarded) == #[2]

/-! ## `commonAncestorBlocks` — proof-irrelevance gates the split

Graph: `1→2, 1→3`. Query `{2, 3}` shares the single common ancestor `1`. If `1` is treated as
proof-irrelevant (ignored for connectivity), `2` and `3` have no shared non-ignored ancestor ⇒
they SPLIT into two blocks; otherwise they stay one meetable block. -/
def gBlocks : Digraph Nat := (({} : Digraph Nat).insertEdge 1 2).insertEdge 1 3

#guard (gBlocks.condense.commonAncestorBlocks {2, 3} (· == 1)).size == 2        -- 1 ignored ⇒ split
#guard (gBlocks.condense.commonAncestorBlocks {2, 3} (fun _ => false)).size == 1 -- 1 kept ⇒ one block
