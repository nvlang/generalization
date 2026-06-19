/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
module

public import Lean.Expr
public import Lean.Environment
public import Lean.Meta.Basic
public import GeneralizationLinter.Helpers.Digraph
public import GeneralizationLinter.Helpers.Canonicalization

/-!
TODO: Module docstring.
-/

open Lean Meta

public structure ClassDag.Vertex where
  /--
  Name of the typeclass.

  Example:
  * `Module R M` → `Module`
  -/
  name : Name

  /--
  Arguments, with constants passed through and everything else canonicalized to
  bvars. For the bvars, the only information that is preserved is which, if any,
  of the arguments were equal to one another.

  Examples:
  * `Module R M` → `[bvar 0, bvar 1]`
  * `SomeClass α β γ β` → `[bvar 0, bvar 1, bvar 2, bvar 1]`
  * `Pow α ℕ` → `[bvar 0, ℕ]`
  * `OfNat α 1` → `[bvar 0, 1]`
  -/
  argsCollapsed : Array Expr
  deriving BEq, Hashable

public abbrev ClassDag := GeneralizationLinter.Digraph ClassDag.Vertex

namespace ClassDag

/--
Convert an `Expr` like `Module R M` to a vertex ``{ name := `Module,
argsCollapsed := [.bvar 0, .bvar 1]}``.
-/
public def toVertex (e : Expr) : MetaM Vertex := do
  let c ← (canonArg e).run' ({}, 0)
  return { name := e.getAppFn.constName?.getD .anonymous, argsCollapsed := c.getAppArgs }

public def splitForalls (e : Expr)
    (acc : Array (Name × BinderInfo × Expr) := #[]) :
    Array (Name × BinderInfo × Expr) × Expr :=
  match e with
  | .forallE n t body bi => splitForalls body (acc.push (n, bi, t))
  | _ => (acc, e)

public def extractEdge? (name : Name) : MetaM (Option (Vertex × Vertex)) := sorry

public def buildClassDag : MetaM ClassDag := sorry
