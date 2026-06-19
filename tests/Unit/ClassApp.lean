/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
import Lean
import GeneralizationLinter.Helpers.ClassApp

/-!
# Unit tests: class-application canonicalization

Pins `toClassApp`'s `argsCollapsed`, which maps each *explicit* class argument to a
`bvar` by first occurrence — preserving *which* arguments were equal while keeping
concrete arguments/literals as-is (see the `ClassApp` docstring). This is Plotkin
anti-unification of the carrier slots.

ASSUMED CONTRACT (v4): `toClassApp : Expr → MetaM ClassApp` (now MetaM + whnf-based,
so reducible aliases unfold) with field `argsCollapsed : Array Expr` (via
`ClassApp extends Vertex`). Inputs are real elaborated class applications (extracted
from an instance binder), so the explicit-vs-instance arity is whatever the kernel
says — no hand-built universes needed.
-/

open Lean Meta
open GeneralizationLinter

/-- Assert the canonicalized args of `decl`'s first instance-implicit binder.

`toClassApp` runs INSIDE the `forallTelescopeReducing`, while the binder's free
variables are still in scope — canonicalizing the binder type outside the telescope
would hit unknown free variables. -/
def expectCollapsed (decl : Name) (expected : Array Expr) : MetaM Unit := do
  let info ← getConstInfo decl
  forallTelescopeReducing info.type fun args _ => do
    for a in args do
      if (← a.fvarId!.getDecl).binderInfo == .instImplicit then
        let ca ← toClassApp (← a.fvarId!.getType)
        unless ca.argsCollapsed == expected do
          throwError "{decl}: expected argsCollapsed {expected}, got {ca.argsCollapsed}"
        return
    throwError "no instance-implicit binder in {decl}"

/-- A toy class with four *explicit* type arguments — to test ordering + repeats. -/
class Cls (a b c d : Type) where

-- C1 — distinct + repeated args: `Cls α β γ β` ↦ `[bvar 0, bvar 1, bvar 2, bvar 1]`.
theorem c1_ex {α β γ : Type} [Cls α β γ β] : True := trivial
#eval expectCollapsed ``c1_ex #[.bvar 0, .bvar 1, .bvar 2, .bvar 1]

-- C2 — a concrete argument is preserved verbatim: `Pow α ℕ` ↦ `[bvar 0, ℕ]`.
theorem c2_ex {α : Type} [Pow α Nat] : True := trivial
#eval expectCollapsed ``c2_ex #[.bvar 0, .const ``Nat []]

-- C3 — all-equal args (this is what feeds the heterogeneous→homogeneous collapse):
-- `HMul α α α` ↦ `[bvar 0, bvar 0, bvar 0]`.
theorem c3_ex {α : Type} [HMul α α α] : True := trivial
#eval expectCollapsed ``c3_ex #[.bvar 0, .bvar 0, .bvar 0]
