/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
module

public import Lean.Declaration
public import Lean.Elab.Term.TermElabM
import Lean.Elab.SyntheticMVars

public import GeneralizationLinter.Analysis.Candidates
import GeneralizationLinter.Analysis.ReSynth

open Lean Meta Elab Term

namespace GeneralizationLinter


/-!
# Verification

This module concerns itself with elaborating a weakened term (usually the proof term of a theorem)
and type-checking the result against some expected type (usually the conclusion of a theorem). This
is used to verify a weakening candidate before it is ever suggested. The goal is to never emit a
single false positive, i.e., an erroneous suggestion.
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
    try weakeningResynthesizable declInfo.type val c.binder.idx c.replacements catch _ => return false


/--
Convert weakenings for which `replacementsRedundant` flagged every replacement as redundant to
drops. Note that the returned array may be smaller than `candidates`. Furthermore, if `verify :=
true`, weakenings that are converted to drops but then don't pass `weakeningHolds` are removed from
the candidates array.
-/
def reshapeRedundantToDrops (declInfo : ConstantInfo) (verify : Bool) (candidates : Array Candidate) :
    MetaM (Array Candidate) :=
  candidates.filterMapM fun c => do
    if c.replacements.isEmpty then return some c
    unless (← replacementsRedundant declInfo.type c.binder.idx c.replacements) do return some c
    let d := { c with shape := .drop }
    if !verify then return some d
    return if (← weakeningHolds declInfo d) then some d else none


/--
Filter out candidates in `candidates` that propose replacing a binder with the conclusion of the
targeted declaration.

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
Return the conclusion of a declaration with type `declType` as a `Key`, wrapped as an `Option`.
If the conclusion isn't a class application, then `none` is returned.
-/
def conclusionKey? (declType : Expr) : MetaM (Option Key) :=
  forallTelescope declType fun _ concl => do
    if (← isClass? concl).isSome then
      (try some <$> toKey (← whnf concl) catch _ => return none)
    else return none


/-- Returns unverified weakening suggestion candidates for a given declaration. -/
public def guardedCandidates (config : LinterConfig) (G : ClassGraph) (declInfo : ConstantInfo) :
    MetaM (Array Candidate) := do
  let some val := declInfo.value? (allowOpaque := true) | return #[]
  let binders ← getTargetedBinders declInfo.type
  if binders.isEmpty then return #[]
  let chains ← getMIChains binders declInfo.type val
  let reqs ← getReqs binders chains
  let mut candidates := mcaCandidates G binders reqs config (includeSubsumers := config.subsumption)
  if config.conclusionGuard then
    candidates := refuseConclusionAssumers (← conclusionKey? declInfo.type) candidates
  if config.redundancyGuard then
    candidates ← reshapeRedundantToDrops declInfo config.verify candidates
  return candidates


/-! ## Recompile -/

public structure SourceIntact where
  /--
  `true` if the declaration's binders wouldn't have to be modified after applying the weakening,
  `false` if they _might_ would have to be modified.
  -/
  binders : Bool
  /--
  `true` if the declaration's conclusion would not have to be modified after applying the weakening,
  `false` if it (almost certainly) would.
  -/
  concl : Bool
  /--
  `true` if the declaration's body (i.e., value) wouldn't have to be modified after applying the
  weakening, `false` if it (almost certainly) would.
  -/
  body : Bool
deriving Inhabited, BEq

public def SourceIntact.all (si : SourceIntact) : Bool := si.binders && si.concl && si.body


/--
Some weakenings may be genuine weakenings, but require modifications in the binders', conclusion's,
or value's (i.e., proof term's) source code. We specify which parts don't need modifications and
which parts do (or might) in the `parts` argument passed to the `.holds` "grade".

If verification is turned off, the `.unverified` "grade" is assigned instead.
-/
public inductive WeakeningGrade where
  /--
  Example: `.holds { binders := true, concl := true, body := true }` indicates that applying the
  weakening would require no additional modifications.
  -/
  | holds (parts : SourceIntact)
  | unverified -- For experimental ablation measurements.
deriving Inhabited, BEq


/-- Source code (`Syntax`) of a declaration and its value. -/
public structure DeclSource where
  body : Syntax
  concl? : Option Syntax := none
  binders : Array Syntax := #[]
deriving Inhabited


/--
Given a weakened declaration `W` of the form `‹binders› : concl` (where `concl` is the same as the
original declaration's), re-elaborate the declaration's value's source code (`src.body`, usually
corresponding to a proof term) into `val` and type-check that we have `val : concl`. Return `some
val` if successful, or `none` otherwise.
-/
public def recompiledAgainst? (W : Expr) (src : DeclSource) (levelNames : List Name := []) : TermElabM (Option Expr) :=
  suppressingDiagnostics do
  try withLevelNames ((← getLevelNames) ++ levelNames) do
    -- `depth?` tells `Meta.forallBoundedTelescope` when to stop telescoping, so that `concl` may
    -- actually match `src.concl?`.
    let attempt (depth? : Option Nat) : TermElabM (Option Expr) := try
        Meta.forallBoundedTelescope W depth? fun ys concl => do
          -- Re-elaborate value source code into `val`. Note that `elabTermAndSynthesize` benefits from
          -- receiving the expected type (in this case `concl`, passed as `some concl`), since without
          -- it most (all?) instance synthesis goals would remain unknown metavariables.
          let val ← elabTermAndSynthesize src.body (some concl)
          -- Check that `val : concl`.
          unless ← Meta.isDefEq (← Meta.inferType val) concl do return none
          -- `val` still mentions `ys` as loose fvars, so we re-abstract them to turn `val` into a
          -- closed term of type `W`.
          let val ← instantiateMVars (← Meta.mkLambdaFVars ys val)
          if val.hasSorry || val.hasExprMVar then return none
          discard <| Meta.check val
          return some val
      -- We don't want a timeout here to lead to a claim that "the body would have to be modified"
      -- (we don't know whether that's true or not at this point), but rather just to dropping the
      -- candidate altogether. We'd rather be quiet than emit suggestions with possibly false claims
      -- attached to them.
      catch e => if e.isRuntime then throw e else return none
    if let some val ← attempt none then return some val
    let some conclStx := src.concl? | return none
    let depth? ← try
        Meta.forallTelescope W fun ys _ => do
          -- Elaborate conclusion syntax, which is our ground truth.
          let c ← withoutErrToSorry (elabTermAndSynthesize conclStx none)
          let rec foralls : Expr → Nat
            | .forallE _ _ b _ => foralls b + 1
            | _ => 0
          -- ∀-arity of conclusion.
          let k := min (foralls c) ys.size
          -- ∀-arity = 0 ⟹ we don't need to worry about `Meta.forallBoundedTelescope` having to stop
          -- telescoping at any point.
          return if k == 0 then none else some (ys.size - k)
      -- As before, a timeout here shouldn't be taken to mean that "the body would have to be
      -- modified".
      catch e => if e.isRuntime then throw e else return none
    let some depth := depth? | return none
    attempt (some depth)
  -- As before, a timeout here shouldn't be taken to mean that "the body would have to be modified".
  catch e => if e.isRuntime then throw e else return none


/--
Check that re-elaborated conclusion is definitionally equal to the old conclusion.

---
**Implementation notes**

`forallTelescope W` strips every `∀` from `W`, even ones that may actually belong to the
conclusion of `W`, which we don't want. So we consult `conclStx` and check how many leading `∀`s it
has, and re-abstract precisely that number of the telescoped `W`'s trailing binders.

For example, if the signature were `[Group α] (a b : α) : ∀ (c : α), a = b → b = c → a = c`, then
`args` would be `#[inst, a, b, c, t₁, t₂]`, where `inst : Group α`, `t₁ : a = b`, and `t₂ : b = c`
would in truth be dynamically-generated hygienic binder names, and `shortConcl` would be `a = c`.
Meanwhile, `conclStx = ‹∀ (c : α), a = b → b = c → a = c›`, so it can tell us that the "real"
conclusion actually has 3 leading `∀`s (corresponding to `c`, `t₁`, and `t₂`).

Now, let's pretend that `Group α` got weakened to `Monoid α`. Then `newConcl = ‹∀ (c : α), a = b → b
= c → a = c›` (note that we're using the `‹›` brackets are being used both for `Syntax` and
`Expr`s). We now want to check that `newConcl` matches the old conclusion, but only have the
`shortConcl` version of the old conclusion. Hence, we extract the last 3 arguments (we know it's 3
because that's how many leading `∀`s `conclStx` has) from `args` (which were telescoped from the old
signature) and build a forall-expression, using them as the arguments and `shortConcl` as the
conclusion, which yields `∀ (c : α) (t₁ : a = b) (t₂ : b = c), a = c`. We then check whether this
"full" old conclusion `Expr` is definitionally equal to `newConcl`, and receive a verdict that is
informative to us, and not simply `false` because of a mismatch in `∀`-arity of the expressions.
-/
public def conclSourceHolds (W : Expr) (conclStx : Syntax) (levelNames : List Name := []) :
    TermElabM Bool :=
  suppressingDiagnostics do
  try
    withLevelNames ((← getLevelNames) ++ levelNames) do
      Meta.forallTelescope W fun args shortConcl => do
        let newConcl ← withoutErrToSorry (elabTermAndSynthesize conclStx none)
        -- See implementation notes.
        let rec foralls : Expr → Nat
          | .forallE _ _ b _ => foralls b + 1
          | _ => 0
        let k := min (foralls newConcl) args.size
        Meta.isDefEq newConcl (← Meta.mkForallFVars (args.extract (args.size - k) args.size) shortConcl)
    catch e =>
      -- We don't want a timeout here to lead to a claim that "the conclusion would have to be
      -- modified" (we don't know whether that's true or not at this point), but rather just to
      -- dropping the candidate altogether.
      if e.isRuntime then throw e else return false


/--
Basically just `recompiledAgainst? ∘ weakenedStatementType`; if the given declaration's _value_
post-weakenings re-elaborates and type-checks against the original conclusion, return said value
through a 2-tuple `(W, value)`, where `value : W` is the value in question. Otherwise, return
`none`.
-/
public def recompiledVal? (const : ConstantInfo) (src : DeclSource) (ws : Array (Nat × Array Vertex)) :
    TermElabM (Option (Expr × Expr)) := do
  let some W ← weakenedStatementType const ws | return none
  return (← recompiledAgainst? W src const.levelParams).map (W, ·)


/--
Does any binder in `binders`, _as source code_ (`Syntax`), mention the binder `name`?

---
**Examples**

Suppose we have

```
theorem foo {R M : Type*}
  [inst₁ : Ring R]
  [inst₂ : AddCommMonoid M]
  [inst₃ : @Module R M (@Ring.toSemiring R inst₁) inst₂] : … := …
```

The typical use case for `binderSourceNamesBinder` would be checking whether weakening `[inst₁ :
Ring R]` to `[inst₁ : Semiring R]` would require the user to modify `foo`'s other binders in any
way. To check this, we would call ``binderSourceNamesBinder #[‹[inst₂ : AddCommMonoid M]›, ‹[inst₃ :
@Module R M (@Ring.toSemiring R inst₁) inst₂]›] `inst₁`` and get `true`.

Had we instead had the following instead

```
theorem foo {R M : Type*}
  [inst₁ : Ring R]
  [inst₂ : AddCommMonoid M]
  [inst₃ : Module R M] : … := …
```

then we'd have called ``binderSourceNamesBinder #[‹[inst₂ : AddCommMonoid M]›, ‹[inst₃ : Module R
M]›] `inst₁`` and gotten `false`.

---
**Implementation notes**

For reference:

```
[inst₃ : @Module R M (@Ring.toSemiring R inst₁) inst₂]    [Module R M]
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^    ^^^^^^^^^^^^
`Lean.Parser.Term.instBinder`                             `Lean.Parser.Term.instBinder`
├─ [0] `atom "["`                                         ├─ [0] `atom "["`
├─ [1] `null`                                             ├─ [1] `null`
│  ├─ [0] `ident inst₃`                                   ├─ [2] `Lean.Parser.Term.app`
│  └─ [1] `atom ":"`                                      │  ├─ [0] `ident Module`
├─ [2] `Lean.Parser.Term.app`                             │  └─ [1] `null`
│  ├─ [0] `Lean.Parser.Term.explicit`                     │     ├─ [0] `ident R`
│  │  ├─ [0] `atom "@"`                                   │     └─ [1] `ident M`
│  │  └─ [1] `ident Module`                               └─ [3] `atom "]"`
│  └─ [1] `null`
│     ├─ [0] `ident R`
│     ├─ [1] `ident M`
│     ├─ [2] `Lean.Parser.Term.paren`
│     │  ├─ [0] `Lean.Parser.Term.hygienicLParen`
│     │  │  ├─ [0] `atom "("`
│     │  │  └─ [1] `hygieneInfo`
│     │  │     └─ [0] `ident [anonymous]`
│     │  ├─ [1] `Lean.Parser.Term.app`
│     │  │  ├─ [0] `Lean.Parser.Term.explicit`
│     │  │  │  ├─ [0] `atom "@"`
│     │  │  │  └─ [1] `ident Ring.toSemiring`
│     │  │  └─ `null`
│     │  │     ├─ [0] `ident R`
│     │  │     └─ [1] `ident inst₁`
│     │  └─ [2] `atom ")"`
│     └─ [3] `ident inst₂`
└─ [3] `atom "]"`
```
-/
public def binderSourceNamesBinder (binders : Array Syntax) (name : Name) : Bool :=
  binders.any fun b =>
    let args := b.getArgs
    -- For many (most?) binders, `searched` is just `#[b[2], b[3]]` (see implementation note above).
    let searched := if args.size ≥ 3 then args.extract 2 args.size else args
    -- See if we can find any identifier matching `name`.
    searched.any fun arg => (arg.find? fun s => (s.isIdent && !name.hasMacroScopes &&
        !name.isAnonymous && s.getId.eraseMacroScopes.getRoot == name)).isSome


/--
If `budget < maxHeartbeats`, run `x` with `maxHeartbeats` lowered to `budget`. Otherwise, just run
`x` with the existing `maxHeartbeats`.

If a runtime (or other non-interrupt) exception occurs while running `x`, it is caught and `dflt`
("default") is returned.

If `budget` is `0`, runs `x` directly without any restrictions or exception handling.
-/
public def withHeartbeatBudget {α : Type} (budget : Nat) (dflt : α) (x : TermElabM α) :
    TermElabM α := do
  if budget == 0 then return ← x
  let ambient := (← readThe Core.Context).maxHeartbeats
  let effectiveMax := if ambient == 0 then budget else min budget ambient
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxHeartbeats := effectiveMax })
      -- `withCurrHeartbeats` resets the heartbeat budget. #TODO
      (withCurrHeartbeats x))
    (fun _ => pure dflt)

public structure GradedWeakening where
  candidate : Candidate
  grade : WeakeningGrade
deriving Inhabited


/--
Given a declaration with constant info `const` and value source code `src.body` (as well as a linter
config and class graph), return an array of verified, graded weakenings that could be applied to the
declaration.
-/
public def gradedWeakenings (cfg : LinterConfig) (graph : ClassGraph) (const : ConstantInfo)
    (src : DeclSource) : TermElabM (Array GradedWeakening) := do
  let candidates ← withHeartbeatBudget cfg.generationHeartbeats #[] (guardedCandidates cfg graph const)
  if candidates.isEmpty then return #[]
  -- Get the binder names, i.e., for `[inst : Monoid M]`, this would be `` `inst ``. Note that
  -- `TargetedBinder.origName` is the name of the _class_, i.e., for `[inst : Monoid M]`, it would
  -- be `` `Monoid ``.
  let binderNames ← targetedBinderTelescope const.type fun lds _ => pure (lds.map (·.userName))
  let mut accepted : Array (Nat × Array Vertex) := #[]
  let mut graded : Array GradedWeakening := #[]
  for candidate in candidates do
    let ws := accepted.push (candidate.binder.idx, candidate.replacements)
    let g? ← withHeartbeatBudget cfg.perCandidateHeartbeats none do
      -- For experimental ablation measurements only.
      if !cfg.verify then return some { candidate, grade := .unverified }
      -- `W` is `const` with each weakening in `ws` (i.e., possibly more than one weakening)
      -- applied.
      let some W ← weakenedStatementType const ws | return none
      -- Compute weakening grade.
      let bodyG := (← recompiledAgainst? W src const.levelParams).isSome
      if !bodyG then
        if !accepted.isEmpty then return none
        unless ← weakeningHolds const candidate do return none
      let conclG ← match src.concl? with
        | some concl' => conclSourceHolds W concl' const.levelParams
        | none => pure false
      let bindersG := match binderNames[candidate.binder.idx]? with
        | some n => !src.binders.isEmpty && !binderSourceNamesBinder src.binders n
        | none => false
      return some {
        candidate,
        grade := .holds { binders := bindersG, concl := conclG, body := bodyG }
      }
    if let some g := g? then
      accepted := ws
      graded := graded.push g
  return graded
