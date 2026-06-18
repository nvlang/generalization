/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
module

public import Lean.Expr
public import GeneralizationLinter.Helpers.ClassDag

/-!
TODO: Module docstring.
-/

open Lean

/--
A specific class application parsed at runtime.
-/
public structure ClassApp extends ClassDag.Vertex where
  /--
  All arguments (explicit, implicit, strict implicit, and instance implicit
  arguments), without canonicalization. Used to construct the suggestion
  candidate.
  -/
  argsExact : Array Expr

/--
Given an `Expr` of a class application, parse it into a ClassApp record.

PRECONDITION:
* `Expr` must be a class application. It should've been extracted from an
  instance implicit binder of a theorem/lemma.
-/
public def toClassApp (e: Expr) : MetaM ClassApp := do
  let ⟨name, argsCollapsed⟩ ← ClassDag.toVertex e
  return { name, argsCollapsed, argsExact := e.consumeMData.getAppArgs }
