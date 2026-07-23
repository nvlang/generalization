/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
module

public import GeneralizationLinter.Helpers.Digraph
public import Lean.Data.Options

namespace GeneralizationLinter
open GeneralizationLinter.Digraph.Condensation (AbsencePolicy)

/-!
# Options

Configurable options for the typeclass generalization linter.
-/

/--
Controls whether typeclass weakenings that would involve splitting a single hypothesis into two
weaker ones should be suggested. Suggested weakenings that split typeclass hypotheses can violate
diamond coherence. Measures are in place to significantly reduce the frequency of such false
positives, but they do not eliminate them, which is why this option is set to `.forbid` by default.
-/
public inductive SplitPolicy where
  /-- Forbid weakenings that would split a typeclass hypothesis up. -/
  | forbid
  /--
  Allow weakenings that would split a typeclass hypothesis up. However, if a different weakening is
  available which would not split up the typeclass hypothesis, choose that weakening instead (even
  if it is technically less general).
   -/
  | allow
  /--
  Always suggest the most general weakening, even if that means suggesting a split where a less
  general non-splitting weakening would be available.
  -/
  | prefer
  deriving Inhabited

public def SplitPolicy.ofString? : String → Option SplitPolicy
  | "forbid" => some .forbid
  | "allow"  => some .allow
  | "prefer" => some .prefer
  | _        => none

/--
Configuration for the typeclass generalization linter.
-/
public structure LinterConfig where
  /--
  Establishes how classes that are not vertices of the class graph should be handled.
  -/
  absencePolicy : AbsencePolicy := .failClosed
  /--
  How many heartbeats the linter may spend analyzing a single declaration. Set this to 0 to remove
  this limit. The default value is `4_000_000` (4 million), which should suffice for around 88% of
  emissions. Higher values increase both maximum latency and coverage; for example, a value of
  `20_000_000` should suffice for around 98% of emissions.
  -/
  perDeclHeartbeats : Nat := 4_000_000
  /--
  Controls whether typeclass weakenings that would involve splitting a single hypothesis into two
  weaker ones should be suggested.

  Setting this option to `.allow` will make the linter suggest splitting a typeclass hypothesis only
  if it could not be weakened otherwise. Setting this option to `.prefer` will make the linter
  always suggest the most general weakening, even if that means suggesting a split where a less
  general non-splitting weakening would be available.

  **Note:** Suggested weakenings that split typeclass hypotheses can violate diamond coherence.

  **Note:** The user can set this property via `set_option generalizeTypeclasses.split "…"`, where …
  is `forbid`, `allow`, or `prefer` (note: no dot in front).
  -/
  splitPolicy : SplitPolicy := .forbid

  -- Options for experimental ablation measurements.
  verify : Bool := true
  subsumption : Bool := true
  conclusionGuard : Bool := true
  vacuityGuard : Bool := true

deriving Inhabited


public register_option linter.generalizeTypeclasses : Bool := {
    defValue := false,
    descr := "flag non-explicit typeclass hypotheses that could be weakened in-place without
      requiring further modifications."
}

public register_option generalizeTypeclasses.split : String := {
  defValue := "forbid"
  descr := "controls whether typeclass weakenings that would involve splitting a single hypothesis
    into two weaker ones should be suggested. Suggested weakenings that split typeclass hypotheses
    can violate diamond coherence. Measures are in place to significantly reduce the frequency of
    such false  positives, but they do not eliminate them, which is why this option is set to
    \"forbid\" by default. Setting this option to \"allow\" will make the linter suggest splitting
    a typeclass hypothesis only if it could not be weakened otherwise. Setting this option to
    \"prefer\" will make the linter always suggest the most general weakening, even if that means
    suggesting a split where a less general non-splitting weakening would be available."
}

public register_option generalizeTypeclasses.targetImplicit : Bool := {
  defValue := true,
  descr := "controls whether implicit and strict implicit binders should also be scanned for
    potential weakenings. Instance implicit binders are always scanned if the linter is active.
    Note that, unlike for instance implicit binders, the linter does not provide a code action for
    suggested weakenings of implicit or strict implicit binders."
}

public register_option generalizeTypeclasses.perDeclHeartbeats : Nat := {
  defValue := 4_000_000,
  descr := "per-declaration heartbeat budget for the typeclass linter's analysis."
}

-- This option will (almost definitely) not be part of the final API. It is used for thesis
-- experiments.
public register_option generalizeTypeclasses.verify : Bool := {
  defValue := true,
  descr := "[Warning: disabling this option is experimental]. Whether suggested weakenings should be
    verified."
}

-- This option will (almost definitely) not be part of the final API. It is used for thesis
-- experiments.
public register_option generalizeTypeclasses.subsumption : Bool := {
  defValue := true,
  descr := "[Warning: disabling this option is experimental]. Whether the subsumption should be used
    when querying the class graph."
}

-- This option will (almost definitely) not be part of the final API. It is used for thesis
-- experiments.
public register_option generalizeTypeclasses.conclusionGuard : Bool := {
  defValue := true,
  descr := "[Warning: disabling this option is experimental]. Whether weakenings that result in the
    conclusion being assumed should be blocked."
}

-- This option will (almost definitely) not be part of the final API. It is used for thesis
-- experiments.
public register_option generalizeTypeclasses.vacuityGuard : Bool := {
  defValue := true,
  descr := "[Warning: disabling this option is experimental]. Whether weakenings that are detected
    to be vacuous should be blocked. Not all vacuity is detected."
}

public register_option linter.generalizeUniverses : Bool := {
  defValue := false,
  descr := "flag type binders that are pinned to a concrete universe but could be
    made universe-polymorphic without requiring further modifications."
}

public def linterConfigOfOptions (opts : Lean.Options) : LinterConfig :=
  {
    splitPolicy := (SplitPolicy.ofString? (generalizeTypeclasses.split.get opts)).getD .forbid,
    perDeclHeartbeats := generalizeTypeclasses.perDeclHeartbeats.get opts,
    verify := generalizeTypeclasses.verify.get opts,
    subsumption := generalizeTypeclasses.subsumption.get opts,
    conclusionGuard := generalizeTypeclasses.conclusionGuard.get opts,
    vacuityGuard := generalizeTypeclasses.vacuityGuard.get opts
  }
