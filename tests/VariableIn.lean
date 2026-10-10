/-
Copyright (c) 2026 Harald Husum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Husum
-/
module

public meta import GeneralizationLinter.Frontend.Linter
public meta import GeneralizationLinter.Analysis.Options
public meta import GeneralizationLinter.Analysis.Replay
public meta import GeneralizationLinter.Analysis.Verify
public meta import Lean.Elab.GuardMsgs

/-! # Declaration-local variables

These regressions check verified suggestions, reconstruction of variables from the weakened
declaration, source-binder grading, and the interaction with other declaration wrappers.
-/

public section

namespace VariableInTest

class Parent (α : Type) where
  op : α → α

class Child (α : Type) extends Parent α where
  extra : α

set_option linter.generalizeTypeclasses true

/--
warning: the `[Child α]` hypothesis of `VariableInTest.unwrapped` can be weakened to `Parent α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
theorem unwrapped {α : Type} [Child α] (a : α) : Parent.op a = Parent.op a := rfl

section
variable {α : Type}

/--
warning: the `[Child α]` hypothesis of `VariableInTest.localInstance` can be weakened to `Parent α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
variable [Child α] in
theorem localInstance (a : α) : Parent.op a = Parent.op a := rfl

end

set_option linter.generalizeTypeclasses false

-- All local variables, including the type and the value used in the body, must be recovered from
-- the declaration. The innermost option wins even across variable/open wrappers.
/--
warning: the `[Child α]` hypothesis of `VariableInTest.nested` can be weakened to `Parent α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
variable {α : Type} in
set_option linter.generalizeTypeclasses false in
open Parent in
variable [Child α] (a : α) in
set_option linter.generalizeTypeclasses true in
theorem nested : op a = op a := rfl

-- Local options must not leak to the next declaration.
#guard_msgs in
theorem afterNested {α : Type} [Child α] (a : α) : Parent.op a = Parent.op a := rfl

set_option linter.generalizeTypeclasses true

#guard_msgs in
variable {α : Type} [Child α] (a : α) in
set_option linter.generalizeTypeclasses false in
theorem disabled : Parent.op a = Parent.op a := rfl

-- The reference to `inst.toParent` occurs only in a variable wrapper, not in the declaration's
-- own binders. It prevents claiming that the original binder source can be kept intact.
/--
warning: the `[Child α]` hypothesis of `VariableInTest.dependent` can be weakened to `Parent α`, but its binders might have to be modified.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
variable {α : Type} [inst : Child α] (a : α)
    (h : @Parent.op α inst.toParent a = @Parent.op α inst.toParent a) in
include h in
theorem dependent : Parent.op a = Parent.op a := h

-- The existing refusal policy for other wrappers remains in force.
#guard_msgs in
variable {α : Type} [Child α] (a : α) in
attribute [local simp] unwrapped in
theorem refused : Parent.op a = Parent.op a := rfl

-- Omits remain suppressed by default, even when nested beneath a variable wrapper.
#guard_msgs in
variable {α : Type} [Child α] [Inhabited α] (a : α) in
omit [Inhabited α] in
theorem omitted : Parent.op a = Parent.op a := rfl

/--
warning: the `[Child α]` hypothesis of `VariableInTest.acceptedOmit` can be weakened to `Parent α`. This declaration's scope has one or more variables omitted from it, which means that the suggested weakening may require the declaration or its value to be modified, or the omit command to be removed, to be valid.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
variable {α : Type} [Child α] [Inhabited α] (a : α) in
set_option generalizeTypeclasses.acceptOmits true in
omit [Inhabited α] in
theorem acceptedOmit : Parent.op a = Parent.op a := rfl

section
variable {α : Type} [Child α] [Inhabited α]
omit [Inhabited α]

#guard_msgs in
variable (a : α) in
theorem sectionOmitted : Parent.op a = Parent.op a := rfl

end

set_option linter.generalizeTypeclasses false

theorem weakened {α : Type} [Parent α] (a : α) : Parent.op a = Parent.op a := rfl

-- Replaying original variable binders would make this body spuriously pass verification by
-- supplying the very Child instance being weakened. Only the weakened telescope may supply it.
open Lean Elab Command Term GeneralizationLinter in
run_cmd liftTermElabM do
  let const ← getConstInfo ``weakened
  -- Parse as user source so its identifiers can refer to the reconstructed telescope variables.
  let source (body : String) : TermElabM DeclSource := do
    let .ok cmd := Parser.runParserCategory (← getEnv) `command
        ("variable {α : Type} [Child α] (a : α) in " ++
          "theorem unused : Parent.op a = Parent.op a := " ++ body)
      | throwError "could not parse test declaration"
    let some (wrappers, decl) := peelWrappers? cmd
      | throwError "variable wrapper was refused"
    let some rawBody ← bodyTermOfDeclVal? (declValNodes decl)[0]!
      | throwError "missing test declaration body"
    return { body := rewrapTerm wrappers rawBody }
  let intact ← source "by exact @Eq.refl α (Parent.op a)"
  unless (← recompiledAgainst? const.type intact).isSome do
    throwError "verification failed to reconstruct the weakened local variables"
  let src ← source "by have _ := (inferInstance : Child α); rfl"
  if (← recompiledAgainst? const.type src).isSome then
    throwError "verification reintroduced the original Child hypothesis"

end VariableInTest
