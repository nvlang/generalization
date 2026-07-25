/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
module

public import GeneralizationLinter.Core.ReSynth
open Lean Meta Elab

namespace GeneralizationLinter

/-!
# Verification

-/

/--
Run `act` quietly. When we run a verification gate, candidates that are rejected would emit warnings
that we don't want to bother the user with.

---
**Implementation notes**

We turn off `Elab.async` because asynchronicity would make it impossible for us to ensure we capture
the emitted messages.
-/
public def suppressingDiagnostics {m : Type → Type} {α : Type} [Monad m] [MonadFinally m]
    [MonadWithOptions m] [MonadLiftT CoreM m] (act : m α) : m α :=
  withOptions (fun o => Elab.async.set o false) do
    let savedLog ← Core.getMessageLog
    try act finally Core.setMessageLog savedLog

public def weakeningHolds (declInfo : ConstantInfo) (c : Candidate) : MetaM Bool :=
  suppressingDiagnostics do
    let some val := declInfo.value? (allowOpaque := true) | return false
    try verifyWeakening declInfo.type val c.binder.idx c.replacements catch _ => return false

public structure ConfirmedWeakening where
  private mk ::
  /-- A verified weakening candidate. -/
  candidate : Candidate

/--
Return the conclusion of a declaration with type `declType` as a `Key`, wrapped as an `Option`.
If the conclusion isn't a class application, then `none` is returned.
-/
def conclusionKey? (declType : Expr) : MetaM (Option Key) :=
  forallTelescope declType fun _ concl => do
    if (← isClass? concl).isSome then
      (try some <$> toKey (← whnf concl) catch _ => return none)
    else return none

/--
Filter out candidates in `candidates` that propose replacing a binder with the conclusion of the
targeted dclaration.

---
**Example**

A lemma `lemma {G : Type*} [Group G] : Monoid G` should not have `Group G` weakened to `Monoid G`.
-/
def refuseConclusionAssumers (concl? : Option Key) (candidates : Array Candidate) :
    Array Candidate :=
  match concl? with
  -- If conclusion is not a class app, then there's no risk of a weakening targeting it, since our
  -- weakenings are limited to typeclass weakenings. (Universe generalization doesn't present any
  -- risk of assuming the conclusion, because it never introduces or removes a class hypothesis.)
  | none => candidates
  -- If conclusion is a class app, check if any replacement matches the conclusion. If so, drop
  -- candidate.
  | some concl => candidates.filter fun c => c.replacements.all (· != concl.toVertex)

/--
Convert weakenings for which `replacementsRedundant` flagged every replacement as redundant to
drops.
-/
def reshapeRedundantToDrops (declInfo : ConstantInfo) (candidates : Array Candidate) :
    MetaM (Array Candidate) :=
  candidates.filterMapM fun c => do
    if c.replacements.isEmpty then return some c
    unless (← replacementsRedundant declInfo.type c.binder.idx c.replacements) do return some c
    let d := { c with shape := .drop }
    return if (← weakeningHolds declInfo d) then some d else none


/-- Returns unverified weakening suggestion candidates for a given declaration. -/
public def meetCandidates (config : LinterConfig) (G : ClassGraph) (declInfo : ConstantInfo) :
    MetaM (Array Candidate) := do
  let some val := declInfo.value? (allowOpaque := true) | return #[]
  let binders ← getTargetedBinders declInfo.type
  if binders.isEmpty then return #[]
  let chains ← getMIChains binders declInfo.type val
  let reqs ← getReqs binders chains
  let mut candidates := candidates G binders reqs config (includeSubsumers := config.subsumption)
  if config.conclusionGuard then
    candidates := refuseConclusionAssumers (← conclusionKey? declInfo.type) candidates
  if config.redundancyGuard && config.verify then
    candidates ← reshapeRedundantToDrops declInfo candidates
  return candidates

/-- Returns verified weakening suggestions for a given declaration. -/
public def getConfirmedWeakenings (config : LinterConfig) (G : ClassGraph) (declName : Name) :
    MetaM (Array ConfirmedWeakening) := do
  let decl ← getConstInfo declName
  (← meetCandidates config G decl).filterMapM fun c => do
    if ← weakeningHolds decl c then return some (ConfirmedWeakening.mk c) else return none
