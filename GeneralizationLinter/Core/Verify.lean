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
    try verifyWeakening declInfo.type val c.binder.idx c.replacementNames catch _ => return false

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
TODO: example
-/
def refuseConclusionAssumers (concl? : Option Key) (candidates : Array Candidate) :
    Array Candidate :=
  match concl? with
  -- If conclusion is not a class app, then there's no risk of a weakening targeting it, since our
  -- weakenings are limited to typeclass weakenings. (Universe generalization doesn't present any
  -- risk of assuming the conclusion, because universe levels can be neither assumptions nor
  -- conclusions.) TODO: Make sure this is true.
  | none => candidates
  | some concl => candidates.filter fun c =>
      match c.singleWeakening? with
      | some tgt => tgt.toVertex != concl.toVertex -- if weakening target is conclusion, drop candidate
      | none => true -- TODO: Is it safe to assume that splits can't lead to assuming the conclusion?

/--
Returns unverified weakening suggestion candidates for a given declaration.
-/
public def meetCandidates (config : LinterConfig) (G : ClassGraph) (declInfo : ConstantInfo) :
    MetaM (Array Candidate) := do
  let some val := declInfo.value? (allowOpaque := true) | return #[]
  let binders ← getTargetedBinders declInfo.type
  if binders.isEmpty then return #[]
  let chains ← getMIChains binders declInfo.type val
  let reqs ← getReqs binders chains
  let candidates := candidates G binders reqs config (includeSubsumers := config.subsumption)
  if !config.conclusionGuard then return candidates
  return refuseConclusionAssumers (← conclusionKey? declInfo.type) candidates

/--
Returns verified weakening suggestions for a given declaration.
-/
public def getConfirmedWeakenings (config : LinterConfig) (G : ClassGraph) (declName : Name) :
    MetaM (Array ConfirmedWeakening) := do
  let decl ← getConstInfo declName
  (← meetCandidates config G decl).filterMapM fun c => do
    if ← weakeningHolds decl c then return some (ConfirmedWeakening.mk c) else return none
