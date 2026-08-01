/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
module

public import Lean.Data.Options
public import GeneralizationLinter.Graph.Digraph

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
  How many heartbeats the linter may spend verifying a single weakening candidate. Set this to 0 to
  remove this limit.
  -/
  perCandidateHeartbeats : Nat := 4_000_000

  /--
  How many heartbeats the linter may spend analyzing a single declaration and generating weakening
  candidates. Set this to 0 to remove this limit.
  -/
  generationHeartbeats : Nat := 4_000_000

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
  redundancyGuard : Bool := true

deriving Inhabited


public register_option linter.generalizeTypeclasses : Bool := {
    defValue := false,
    descr := "flag theorems with non-explicit typeclass hypotheses that could be weakened."
}

public register_option generalizeTypeclasses.split : String := {
  defValue := "forbid"
  descr := "controls whether typeclass weakenings that would involve splitting a single hypothesis
    into two weaker ones should be suggested. Suggested weakenings that split typeclass hypotheses
    can violate diamond coherence. Measures are in place to significantly reduce the frequency of
    such false positives, but they do not eliminate them, which is why this option is set to
    \"forbid\" by default. Setting this option to \"allow\" will make the linter suggest splitting
    a typeclass hypothesis only if it could not be weakened otherwise. Setting this option to
    \"prefer\" will make the linter always suggest the most general weakening, even if that means
    suggesting a split where a less general non-splitting weakening would be available."
}

public register_option generalizeTypeclasses.targetImplicit : Bool := {
  defValue := true,
  descr := "controls whether implicit and strict implicit binders should also be scanned for
    potential weakenings. Instance implicit binders are always scanned if the linter is active."
}

public register_option generalizeTypeclasses.generationHeartbeats : Nat := {
  defValue := 4_000_000,
  descr := "how many heartbeats the linter may spend analyzing a single declaration and generating
    weakening candidates. Set this to 0 to remove this limit. Defaults to 4_000_000."
}

public register_option generalizeTypeclasses.perCandidateHeartbeats : Nat := {
  defValue := 4_000_000,
  descr := "how many heartbeats the linter may spend verifying a single weakening candidate. Set
    this to 0 to remove this limit. Defaults to 4_000_000."
}

public register_option generalizeTypeclasses.acceptOmits : Bool := {
  defValue := false,
  descr := "whether declarations within `omit … in` commands or within sections with any `omit …`
    commands should be analyzed by the linter. Default: `false`. Warning: For these declarations,
    the linter cannot guarantee that its suggestions will elaborate."
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
  descr := "[Warning: disabling this option is experimental]. Whether subsumption should be used
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
public register_option generalizeTypeclasses.redundancyGuard : Bool := {
  defValue := true,
  descr := "[Warning: disabling this option is experimental]. Whether a specific type of vacuous
    weakenings should become \"drop\" suggestions instead. Not all vacuity is detected."
}

public register_option generalizeTypeclasses.stats : Bool := {
  defValue := false,
  descr := "[For experiments only] log a GL_STATS info message for each linted declaration."
}

public def linterConfigOfOptions (opts : Lean.Options) : LinterConfig :=
  {
    splitPolicy := (SplitPolicy.ofString? (generalizeTypeclasses.split.get opts)).getD .forbid,
    generationHeartbeats := generalizeTypeclasses.generationHeartbeats.get opts,
    perCandidateHeartbeats := generalizeTypeclasses.perCandidateHeartbeats.get opts,
    verify := generalizeTypeclasses.verify.get opts,
    subsumption := generalizeTypeclasses.subsumption.get opts,
    conclusionGuard := generalizeTypeclasses.conclusionGuard.get opts,
    redundancyGuard := generalizeTypeclasses.redundancyGuard.get opts
  }
