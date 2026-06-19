/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
import Mathlib
import GeneralizationLinter.Core.Linter
import GeneralizationLinter.Core.Options

/-!
# Behavioral tests: cross-frame rendering of weakening suggestions

The linter canonicalises every class application to de-Bruijn carrier slots; rendering a
suggestion means mapping those slots back to the user's real binder names. The subtle bugs
all live in that mapping — and especially on the RHS (the weakened-to class), whose canonical
frame can differ from the binder's. These goldens pin the carrier names in the emitted
message, so an internal rewrite cannot silently reintroduce a wrong/garbage name (the printed
text is what a user copy-pastes).

These are PRESENTATION goldens (they pin the message wording, not just head names), so they
live alongside G0/G4 in `Weakening.lean` conceptually but are kept here for focus. Fixtures are
namespaced and declared before the linted theorems so the class DAG sees them; class names
render fully qualified, hence the `CFR.` prefix.

Failure modes each test guards against (found by the old project's audit):
* (1) a relation / second carrier rendered as a Greek placeholder that COLLIDES with the type
  carrier (`[IsWellOrder β s]` shown as `[IsWellOrder β β]`);
* (2) a class with an implicit type param + explicit relation rendering the implicit type
  instead of the explicit arg (`Std.Trichotomous β` for `Std.Trichotomous s`);
* (3) a forgetful chain filling an inst slot BEFORE a carrier, desyncing canonical indices so
  the carrier prints a hygienic `_hyg` name;
* (4) CROSS-FRAME: a forgetful edge that REORDERS carriers — the RHS must use the candidate's
  order (`Commute' N M`), not the binder's (`Commute' M N`, which is also unsound);
* (5) CROSS-FRAME: an interleaved instance binder (`Strong X [Inst X] Y`) whose hygienic name
  must NOT leak onto the RHS carrier.
-/

namespace CFR

/-! ## Fixtures: self-contained toy classes (kept in-env so the class DAG sees them) -/

-- (1)/(2) a two-carrier class whose 2nd carrier is a RELATION.
class FooRel (α : Type) (r : α → α → Prop) : Prop where ok : True
class BarRel (α : Type) (r : α → α → Prop) : Prop where ok : True
class BazRel {α : Type} (r : α → α → Prop) : Prop where ok : True   -- α IMPLICIT
instance barOfFoo {α} {r : α → α → Prop} [FooRel α r] : BarRel α r := ⟨trivial⟩
instance bazOfFoo {α} {r : α → α → Prop} [FooRel α r] : BazRel r := ⟨trivial⟩
def needBarRel {α} {r : α → α → Prop} [BarRel α r] : True := trivial
def needBazRel {α} {r : α → α → Prop} [BazRel r] : True := trivial

-- (3) chain-preceded carrier: an ambient `[StrongR R]` fills `FooMod`'s `[WeakR R]` slot with
--     a forgetful CHAIN, pushing carrier `M` to a later canonical index.
class WeakR (R : Type) : Prop where ok : True
class StrongR (R : Type) : Prop where ok2 : True
instance strongToWeakR {R} [StrongR R] : WeakR R := ⟨trivial⟩
class FooMod (R : Type) [WeakR R] (M : Type) : Prop where ok : True
class BarMod (R : Type) [WeakR R] (M : Type) : Prop where ok : True
instance barModOfFoo {R} [WeakR R] {M} [FooMod R M] : BarMod R M := ⟨trivial⟩
def needBarMod {R} [WeakR R] {M} [BarMod R M] : True := trivial

-- (4) carrier REORDER across the edge: `BiCompat M N → Commute' N M`.
class Commute' (X Y : Type) : Prop where ok : True
class BiCompat (M N : Type) : Prop where ok : True
instance commOfBi {M N : Type} [BiCompat M N] : Commute' N M := ⟨trivial⟩
def needCommute {X Y : Type} [Commute' X Y] : True := trivial

-- (5) INSTANCE-INTERLEAVE: `Strong X [Inst X] Y` — the inst binder is a bvar.
class Carrier2 (a : Type) : Prop where ok : True
class Weak (X Y : Type) : Prop where ok : True
class Strong (X : Type) [Carrier2 X] (Y : Type) : Prop where ok : True
instance weakOfStrong {X : Type} [Carrier2 X] {Y : Type} [Strong X Y] : Weak X Y := ⟨trivial⟩
def needWeak {X Y : Type} [Weak X Y] : True := trivial

end CFR

/-! ## Presentation goldens -/

-- (1) The relation `r` must render as `r`, not a Greek placeholder colliding with `α`.
set_option linter.generalize true in
/--
warning: `t_relCarrier` has typeclass arguments that could be weakened:
  • [CFR.FooRel α r] ↝ [CFR.BarRel α r]

Note: This linter can be disabled with `set_option linter.generalize false`
-/
#guard_msgs in
theorem t_relCarrier {α} {r : α → α → Prop} [CFR.FooRel α r] : True := CFR.needBarRel (r := r)

-- (2) Candidate has an IMPLICIT type param + EXPLICIT relation: render the explicit `r`.
set_option linter.generalize true in
/--
warning: `t_implicitTypeArg` has typeclass arguments that could be weakened:
  • [CFR.FooRel α r] ↝ [CFR.BazRel r]

Note: This linter can be disabled with `set_option linter.generalize false`
-/
#guard_msgs in
theorem t_implicitTypeArg {α} {r : α → α → Prop} [CFR.FooRel α r] : True := CFR.needBazRel (r := r)

-- (3) A forgetful chain fills the inst slot before carrier `M`; `M` must still render `M`.
set_option linter.generalize true in
/--
warning: `t_chainPreceded` has typeclass arguments that could be weakened:
  • [CFR.FooMod R M] ↝ [CFR.BarMod R M]

Note: This linter can be disabled with `set_option linter.generalize false`
-/
#guard_msgs in
theorem t_chainPreceded {R M : Type} [CFR.StrongR R] [CFR.FooMod R M] : True :=
  CFR.needBarMod (R := R) (M := M)

-- (4) CROSS-FRAME TRAP: the edge swaps carriers. The RHS must render `Commute' N M`
--     (the candidate's order). `Commute' M N` is UNSOUND — it does not synthesise.
set_option linter.generalize true in
/--
warning: `t_reorder` has typeclass arguments that could be weakened:
  • [CFR.BiCompat M N] ↝ [CFR.Commute' N M]

Note: This linter can be disabled with `set_option linter.generalize false`
-/
#guard_msgs in
theorem t_reorder {M N : Type} [CFR.BiCompat M N] : True := CFR.needCommute (X := N) (Y := M)

-- (5) CROSS-FRAME TRAP: the instance binder `[Carrier2 X]` is a bvar; its hygienic name must
--     NOT leak. The RHS carrier must be `B`.
set_option linter.generalize true in
/--
warning: `t_interleave` has typeclass arguments that could be weakened:
  • [CFR.Strong A B] ↝ [CFR.Weak A B]

Note: This linter can be disabled with `set_option linter.generalize false`
-/
#guard_msgs in
theorem t_interleave {A B : Type} [CFR.Carrier2 A] [CFR.Strong A B] : True :=
  CFR.needWeak (X := A) (Y := B)
