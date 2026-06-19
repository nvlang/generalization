/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
import Mathlib
import GeneralizationLinter.Core.Linter
import GeneralizationLinter.Core.Options

/-!
# Behavioral tests: the typeclass-weakening linter (feature parity)

Each behavioral edge case appears **once**, at the cheapest layer that can express it.
Every expected value here was independently checked to type-check (or fail) in real Lean,
so the goldens are correct even before `src/` implements the contract.

ASSUMED CONTRACT (TDD target — names/format adjustable; the tests are the single source
of truth that pins them):

* `GeneralizationLinter.weakeningNames : Name → MetaM (Array (Name × Array Name))` (the v4
  convenience entry, a head-name projection of `lintConst`) — for each binder the linter
  would weaken, `(originalClass, suggestedAntichain)` (by head name). Binders with no
  suggestion are omitted; `#[]` means "no suggestion at all". **It returns the final,
  as-presented result**, i.e. it honors the `linter.generalize.*` gate options in scope.
* Linter option `linter.generalize : Bool` (opt-in) plus gates
  `linter.generalize.{suppressLowValue, suppressVacuous, warnDecidabilityLoss, allowClassSplit,
  contextualAttribution}` (and the `coverStrategy`/`absencePolicy` config). Coupling
  preservation is deferred — see G2 below.
* Warning message format (pinned by the `#guard_msgs` goldens below).
-/

open Lean Meta
open GeneralizationLinter

/-! ## Test harness -/

/-- Order-insensitive, duplicate-free set equality. -/
def sameSet [BEq α] (xs ys : List α) : Bool :=
  xs.length == ys.length && xs.all (ys.contains ·) && ys.all (xs.contains ·)

/-- Order-insensitive equality of weakening results (`original ↦ suggested antichain`). -/
def weakEq (a b : Array (Name × Array Name)) : Bool :=
  a.size == b.size &&
    a.all fun (o, ss) => b.any fun (o', ss') => o == o' && sameSet ss.toList ss'.toList

/-- Assert the linter's suggestions for `decl` (in the current option scope). -/
def expectWeak (decl : Name) (expected : Array (Name × Array Name)) : MetaM Unit := do
  let got ← weakeningNames decl
  unless weakEq got expected do throwError "{decl}: expected {expected}, got {got}"

/-- Assert the linter stays silent on `decl`. -/
def expectSilent (decl : Name) : MetaM Unit := expectWeak decl #[]

/-! ## Fixtures: self-contained toy classes (kept in-env so the class DAG sees them) -/

namespace Toy
-- A "necessity-of-verification" diamond: two converging instance paths to `C`.
class A (α : Type) where a : α → α
class A' (α : Type) extends A α where a' : α → α
class B (α : Type) where b : α → α
class B' (α : Type) extends B α where b' : α → α
class C (α : Type) where c : α → α
instance {α} [A' α] [B α] : C α := ⟨fun x => A'.a' x⟩
instance {α} [A α] [B' α] : C α := ⟨fun x => B'.b' x⟩
end Toy

namespace Toy2
-- A genuine 2-class split: `Tp` is the join of incomparable `Le`, `Ri`.
class Le (α : Type) where l : α
class Ri (α : Type) where r : α
class Tp (α : Type) extends Le α, Ri α
end Toy2

namespace Vac
-- A "vacuous" setup: weakening `S ↝ W` is sound, but a surviving `Foo` re-derives `S`.
class W (α : Type) where w : α
class S (α : Type) extends W α where s : α
class Foo (α : Type) where f : α
instance {α} [Foo α] : S α where
  w := Foo.f
  s := Foo.f
end Vac

/-! ## Positive cases — must suggest a (verified-sound) weakening -/

-- P1 — only the monoid structure of `g` is used.
theorem p1_group {G : Type*} [Group G] (n : ℕ) (g : G) (h : g ^ n = 1) : g ^ (2 * n) = 1 := by
  rw [pow_mul', h, one_pow]
#eval expectWeak ``p1_group #[(``Group, #[``Monoid])]

-- P2 — `add_neg_cancel` bottoms out at `AddGroup` (boundary-checked: SubtractionMonoid fails).
theorem p2_acg {G : Type*} [AddCommGroup G] (a : G) : a + -a = 0 := add_neg_cancel a
#eval expectWeak ``p2_acg #[(``AddCommGroup, #[``AddGroup])]

-- P3 — minimal weakening is the antichain `[Le] [Ri]`; neither alone suffices.
theorem p3_anti {α : Type} [Toy2.Tp α] :
    (Toy2.Le.l : α) = Toy2.Le.l ∧ (Toy2.Ri.r : α) = Toy2.Ri.r := ⟨rfl, rfl⟩
#eval expectWeak ``p3_anti #[(``Toy2.Tp, #[``Toy2.Le, ``Toy2.Ri])]

/-! ## Silence cases — must produce no suggestion (sound-minimal / unsound to weaken) -/

-- S1 — already minimal: `add_comm` genuinely needs commutativity.
theorem s1_min {T : Type*} [AddCommMagma T] (a b : T) : a + b = b + a := add_comm a b
#eval expectSilent ``s1_min

-- S2 (+ S6) — necessity of verification: the naive meet `[A] [B]` cannot build `C α`
-- (each instance path needs one *strong* parent), so the linter must NOT weaken BOTH binders.
theorem diamond_thm {α : Type} [Toy.A' α] [Toy.B' α] (x : α) :
    Toy.A.a x = Toy.A.a x ∧ Toy.B.b x = Toy.B.b x ∧ Toy.C.c x = Toy.C.c x := ⟨rfl, rfl, rfl⟩
#eval show MetaM Unit from do
  let got ← weakeningNames ``diamond_thm
  if got.any (·.1 == ``Toy.A') && got.any (·.1 == ``Toy.B') then
    throwError "necessity-of-verification: proposed weakening BOTH diamond binders (unsound): {got}"

-- S3 — a Prop-valued class (`Fact`) that is genuinely used is never dropped.
theorem s3_fact (p : ℕ) [Fact p.Prime] : p.Prime := Fact.out
#eval expectSilent ``s3_fact

/-! ## Cosmetic gates — suppressed by default, recovered when the gate option is off -/

-- G1 — low value: the sound weakening is to a bare operation class (`AddMonoid ↝ Add`).
theorem g1_lowvalue {M : Type*} [AddMonoid M] (a b : M) : a + b = a + b := rfl
#eval expectSilent ``g1_lowvalue
set_option linter.generalize.suppressLowValue false in
#eval expectWeak ``g1_lowvalue #[(``AddMonoid, #[``Add])]

-- G3 — vacuous: `S ↝ W` is sound but `Foo` re-derives `S`, so it adds no models.
theorem vac_thm {α : Type} [Vac.S α] [Vac.Foo α] : (Vac.W.w : α) = Vac.W.w := rfl
#eval expectSilent ``vac_thm
set_option linter.generalize.suppressVacuous false in
#eval expectWeak ``vac_thm #[(``Vac.S, #[``Vac.W])]

/-! ## Presentation goldens — the ONLY place the message wording is pinned -/

-- G0 — canonical message format.
set_option linter.generalize true in
/--
warning: `p1_group_msg` has typeclass arguments that could be weakened:
  • [Group G] ↝ [Monoid G]

Note: This linter can be disabled with `set_option linter.generalize false`
-/
#guard_msgs in
theorem p1_group_msg {G : Type*} [Group G] (n : ℕ) (g : G) (h : g ^ n = 1) :
    g ^ (2 * n) = 1 := by rw [pow_mul', h, one_pow]

-- G4 — decidability-loss advisory (`LinearOrder ↝ Preorder` drops a `Decidable` carrier).
set_option linter.generalize true in
/--
warning: `g4_msg` has typeclass arguments that could be weakened:
  • [LinearOrder α] ↝ [Preorder α]
    ⚠ This weakening drops [DecidableLE α]; `decide`/`omega` may stop working downstream.

Note: This linter can be disabled with `set_option linter.generalize false`
-/
#guard_msgs in
theorem g4_msg {α : Type*} [LinearOrder α] (a : α) : a ≤ a := le_refl a

/-! ## Deferred edge cases (need design decisions in `src/` before a correct golden exists)

These are real edge cases from the old project, intentionally NOT asserted yet because the
correct expectation depends on the rewrite's still-undesigned internals:

* S4 — banned type-alias prefixes (`Multiplicative`/`Additive`/`OrderDual`): a chain through
  the alias is a rename, not a weakening. Needs the rewrite's instance-chain/alias handling.
* S5 — repeated-argument specialization (`[Module R R]`, canonical key `[bvar 0, bvar 0]`):
  the documented "stay silent" gap. Needs the canonicalized-key lookup to exist.
* G2 — coupling preservation (e.g. `PseudoMetricSpace ↝ [Dist] [TopologicalSpace]`): requires
  a carefully constructed decoupling proof AND the rewrite's curated `couplingBundles` list.
* G5 — explicit-arity formatting (`[IsStrictOrderedRing α]`, not padded with inst slots):
  a message-formatting detail to pin once the printer exists.
-/
