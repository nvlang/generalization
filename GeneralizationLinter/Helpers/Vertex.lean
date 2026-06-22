/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
module

public import Lean.Expr

namespace GeneralizationLinter

/-!
TODO: Module docstring.
-/

open Lean

/-- Describes universe polymorphism (or lack thereof) for vertices. -/
public inductive UniverseLevels
  | polymorphic -- universe-polymorphic
  | concrete (levels : Array Level) -- specific universe levels only
  deriving BEq, Hashable, Inhabited

public structure Vertex where
  /--
  Name of the typeclass.

  Example:
  * `Module R M` → `Module`
  -/
  name : Name

  /--
  Arguments, with constants passed through and everything else canonicalized to
  bvars (though structured carriers keep their structure). For the bvars, the
  only information that is preserved is which, if any, of the arguments were
  equal to one another.

  ---
  **Examples**

  | Class application | `collapsedArgs` | Notes |
  |:----|:----|:----|
  | `Module R M` | `#[bvar 0, bvar 1]` | fvars become bvars |
  | `SomeClass α β γ β` | `#[bvar 0, bvar 1, bvar 2, bvar 1]` | repeated fvars reuse bvar index |
  | `Pow α ℕ` | `#[bvar 0, ℕ]` | bare constant is preserved |
  | `IsTrans α (·=·)` | `#[bvar 0, bvar 1]` | opaque relation becomes bvar |
  | `OfNat α 1` | `#[bvar 0, 1]` | nat literal is preserved |
  | `Monoid (List α)` | `#[List (bvar 0)]` | structure inside carrier is preserved |
  | `Module (α × β) M` | `#[(bvar 0) × (bvar 1), bvar 2]` | structure inside carrier is preserved |
  -/
  collapsedArgs : Array Expr

  /--
  Describes the universe polymorphism (or lack thereof) of the typeclass.
  -/
  universeLevels : UniverseLevels
  deriving BEq, Hashable, Inhabited

/--
Given a vertex `v`, returns the array of vertices that match `v`. This is used
to match non-universe-polymorphic vertices with both the corresponding
non-universe-polymorphic vertex _and_ the corresponding universe-polymorphic
vertex.
-/
public def Vertex.matchingKeys (v : Vertex) : Array Vertex :=
  match v.universeLevels with
  | .polymorphic => #[v]
  | .concrete _ => #[v, { v with universeLevels := .polymorphic }]

/--
A specific class application parsed at runtime.
-/
public structure ClassApp extends Vertex where
  /--
  The concrete terms abstracted by `collapsedArgs`'s bvars: `carriers[k]` is the
  term that `bvar k` stands for.
  -/
  carriers : Array Expr
  deriving Inhabited
