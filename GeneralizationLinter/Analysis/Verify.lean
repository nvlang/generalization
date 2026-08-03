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
Run `act` quietly. When we run a verification gate, candidates that are rejected would emit errors
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

/-
Does the weakened statement `W` imply the original statement `origType`?

The other gates re-synthesize the proof against `W`, which shows the proof still goes through, not
that `W` is more general. Here `W` is applied inside the original's context, where the original's
binders are available, and its conclusion must match.
-/
public def weakenedImpliesOriginal (W origType : Expr) : MetaM Bool :=
  withNewMCtxDepth do
  try
    forallTelescope origType fun xs concl => do
      let (margs, _, wConcl) ← forallMetaTelescope W
      -- what the shared conclusion pins, it pins
      unless ← isDefEq wConcl concl do return false
      for m in margs do
        if ← m.mvarId!.isAssigned then continue
        let ty ← instantiateMVars (← inferType m)
        if (← isClass? ty).isSome then
          -- a class hypothesis must follow from the original's context, where the strong binder is
          -- still in scope as a local instance
          match ← (try trySynthInstance ty catch _ => pure .none) with
          | .some inst => m.mvarId!.assign inst
          | _ => return false
        else
          -- anything else must be supplied by one of the original's own binders
          let some x ← xs.findM? (fun x => do isDefEq (← inferType x) ty) | return false
          m.mvarId!.assign x
      return true
  catch e => if e.isRuntime then throw e else return false


/-
Would the weakened declaration still be admissible as an instance? The linted population includes
registered `instance`s, and weakening a binder can leave an argument synthesis cannot infer. Rather
than replicate Lean's inferrability rule, declare `W` in a throwaway environment and let
`addInstance` compute the synthesization order. Non-instances are admissible by definition.
-/
public def stillAdmissibleInstance (declName : Name) (W : Expr) (levelParams : List Name) :
    MetaM Bool := do
  unless ← isInstance declName do return true
  withoutModifyingEnv do
    try
      let probe := declName ++ `_glAdmissibilityProbe
      addDecl (.axiomDecl { name := probe, levelParams, type := W, isUnsafe := false })
      Meta.addInstance probe .global ((← getInstancePriority? declName).getD 1000)
      return true
    catch e => if e.isRuntime then throw e else return false


public def weakeningHolds (declInfo : ConstantInfo) (c : Candidate) : MetaM Bool :=
  suppressingDiagnostics do
    let some val := declInfo.value? (allowOpaque := true) | return false
    try weakeningResynthesizable declInfo.type val c.binder.idx c.replacements catch _ => return false


/--
Convert weakenings for which `replacementsRedundant` flagged every replacement as redundant to
drops. Note that the returned array may be smaller than `candidates`. Furthermore, if `verify :=
true`, weakenings that are converted to drops but then don't pass `weakeningHolds` are removed from
the candidates array.

---
**Examples**

```
class Foo (α : Type) where
class Bar (α : Type) where
instance {α : Type} [Foo α] : Bar α := ⟨⟩

theorem thm₁ {α : Type} [Foo α] [inst : Bar α] : True := trivial
def thm₂ {α : Type} [inst : Bar α] : Bar α := inst

-- `infoᵢ` is `thmᵢ`'s `ConstantInfo`, `wᵢ = { binder := ‹thmᵢ's [inst : Bar α]›, shape := .weaken
-- ‹Bar #0› }`, and `dᵢ = { wᵢ with shape := .drop }`.
reshapeRedundantToDrops info₁ true #[w₁] = #[d₁]
reshapeRedundantToDrops info₂ true #[w₂] = #[w₂]
reshapeRedundantToDrops info₂ true #[d₂] = #[d₂]  -- as-is: `weakeningHolds info₂ d₂` is `false`
```
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
**Examples**

A lemma `lemma le {G : Type*} [Group G] : Monoid G` should not have `Group G` weakened to `Monoid
G`.

```
-- Suppose that `conclK` is that lemma's conclusion key, i.e., `conclusionKey? ‹lemma's type›` is
-- `some conclK`. Let `cand₁` and `cand₂` be candidates which would weaken its `[Group G]` binder to
-- `Monoid #0` and `Semigroup #0`, respectively.
refuseConclusionAssumers (some conclK) #[cand₁, cand₂] = #[cand₂]
refuseConclusionAssumers none #[cand₁, cand₂] = #[cand₁, cand₂]
```
-/
def refuseConclusionAssumers (conclK? : Option Key) (candidates : Array Candidate) :
    Array Candidate :=
  match conclK? with
  -- If conclusion is not a class app, then there's no risk of a weakening targeting it, since our
  -- weakenings are limited to typeclass weakenings.
  | none => candidates
  -- If conclusion is a class app, check if any replacement matches the conclusion. If so, drop
  -- candidate. Graph vertices are universe-polymorphic while a monomorphic conclusion canonicalizes
  -- to `.concrete`, so we compare against both forms, as `Vertex.witnesses` does when querying.
  | some conclK =>
    let concl := conclK.toVertex
    let conclPoly := { concl with levels := .polymorphic }
    candidates.filter fun c => c.replacements.all fun r => r != concl && r != conclPoly


/--
Return the conclusion of a declaration with type `declType` as a `Key`, wrapped as an `Option`.
If the conclusion isn't a class application, then `none` is returned.

---
**Examples**

```
conclusionKey? ‹∀ {M : Type u} [CommMonoid M], Monoid M› = some {
  name := `Monoid, pattern := #[#0], levels := .polymorphic, subst := #[M], forallArity := 0 }
conclusionKey? ‹∀ {M : Type u} [MulOneClass M] (a : M), a * 1 = a› = none
-- The conclusion's own `∀`s are telescoped away as well.
conclusionKey? ‹∀ {ι : Type} {f : ι → Type} [∀ i, Monoid (f i)], ∀ i, Monoid (f i)› = some {
  name := `Monoid, pattern := #[#0], levels := .concrete #[0], subst := #[f i], forallArity := 0 }
```
-/
def conclusionKey? (declType : Expr) : MetaM (Option Key) :=
  forallTelescope declType fun _ concl => do
    if (← isClass? concl).isSome then
      (try some <$> canonKey (← whnf concl) catch _ => return none)
    else return none


/--
Returns weakening suggestion candidates for a given declaration. These are unverified, except that,
when `config.redundancyGuard` and `config.verify` are both set, candidates reshaped into drops by
`reshapeRedundantToDrops` have been verified (and removed if they failed).
-/
public def guardedCandidates (config : LinterConfig) (G : ClassGraph) (declInfo : ConstantInfo) :
    MetaM (Array Candidate) := do
  let some val := declInfo.value? (allowOpaque := true) | return #[]
  let binders ← getTargetedBinders declInfo.type
  if binders.isEmpty then return #[]
  let chains ← getMIChains binders declInfo.type val
  let reqs ← getReqs binders chains
  let mut candidates :=
    mcaCandidates G binders reqs config (includeSubsumers := config.includeSubsumers)
  if config.conclusionGuard then
    candidates := refuseConclusionAssumers (← conclusionKey? declInfo.type) candidates
  if config.redundancyGuard then
    candidates ← reshapeRedundantToDrops declInfo config.verify candidates
  return candidates


/-! ## Recompile -/

public structure SourceIntact where
  /--
  `true` if no other binder mentions the weakened binder by name, `false` if one does. Note that
  this is a syntactic scan (`bindersMention`), not a re-elaboration: it does not see a binder whose
  type the elaborator filled in from the weakened one.
  -/
  binders : Bool
  /--
  `true` if the declaration's conclusion would not have to be modified after applying the weakening,
  `false` if it might. A `false` records only a failure to confirm: re-elaboration failed, or the
  conclusion's source syntax was unavailable.
  -/
  concl : Bool
  /--
  `true` if the declaration's body (i.e., value) wouldn't have to be modified after applying the
  weakening, `false` if it might. As for `concl`, a `false` is only a failure to confirm.
  -/
  body : Bool
deriving Inhabited, BEq


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
public def recompiledAgainst? (W : Expr) (src : DeclSource) (levelNames : List Name := []) :
    TermElabM (Option Expr) :=
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
          return some (ys.size - k)
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

For example, if the declaration's signature were `[Group α] (a b : α) : ∀ (c : α), a = b → b = c →
a = c` and `Group α` got weakened to `Monoid α`, then `W` would be that signature with `[Monoid α]`
in place of `[Group α]`, so `args` would be `#[α, inst, a, b, c, t₁, t₂]`, where `inst : Monoid α`,
`t₁ : a = b`, and `t₂ : b = c` would in truth be dynamically-generated hygienic binder names, and
`shortConcl` would be `a = c`. Meanwhile, `conclStx = ‹∀ (c : α), a = b → b = c → a = c›`, so it can
tell us that the "real" conclusion actually has 3 leading `∀`s (corresponding to `c`, `t₁`, and
`t₂`).

Now, `newConcl = ‹∀ (c : α), a = b → b = c → a = c›` (note that the `‹›` brackets are being used
both for `Syntax` and `Expr`s). We now want to check that `newConcl` matches the old conclusion, but
only have the `shortConcl` version of the old conclusion. Hence, we extract the last 3 arguments (we
know it's 3 because that's how many leading `∀`s `conclStx` has) from `args` (which were telescoped
from `W`) and build a forall-expression, using them as the arguments and `shortConcl` as the
conclusion, which yields `∀ (c : α) (t₁ : a = b) (t₂ : b = c), a = c`. We then check whether this
"full" old conclusion `Expr` is definitionally equal to `newConcl`, and receive a verdict that is
informative to us, and not simply `false` because of a mismatch in `∀`-arity of the expressions.
-/
public def conclSourceIntact (W : Expr) (conclStx : Syntax) (levelNames : List Name := []) :
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

The typical use case for `bindersMention` would be checking whether weakening `[inst₁ :
Ring R]` to `[inst₁ : Semiring R]` would require the user to modify `foo`'s other binders in any
way. To check this, we would call ``bindersMention #[‹[inst₂ : AddCommMonoid M]›, ‹[inst₃ :
@Module R M (@Ring.toSemiring R inst₁) inst₂]›] `inst₁`` and get `true`.

Had we instead had the following

```
theorem foo {R M : Type*}
  [inst₁ : Ring R]
  [inst₂ : AddCommMonoid M]
  [inst₃ : Module R M] : … := …
```

then we'd have called ``bindersMention #[‹[inst₂ : AddCommMonoid M]›, ‹[inst₃ : Module R
M]›] `inst₁`` and gotten `false`.

```
bindersMention #[‹[inst₁ : Ring R]›] `R = true
bindersMention #[‹[inst₁ : Ring R]›] `inst₁ = false
bindersMention #[‹{R M : Type*}›] `R = false
```

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
│     │  │  └─ [1] `null`
│     │  │     ├─ [0] `ident R`
│     │  │     └─ [1] `ident inst₁`
│     │  └─ [2] `atom ")"`
│     └─ [3] `ident inst₂`
└─ [3] `atom "]"`
```
-/
public def bindersMention (binders : Array Syntax) (name : Name) : Bool :=
  binders.any fun b =>
    let args := b.getArgs
    -- For many (most?) binders, `searched` is just `#[b[2], b[3]]` (see implementation note above).
    let searched := if args.size ≥ 3 then args.extract 2 args.size else args
    -- See if we can find any identifier matching `name`.
    searched.any fun arg => (arg.find? fun s => (s.isIdent && !name.hasMacroScopes &&
        !name.isAnonymous && s.getId.eraseMacroScopes.getRoot == name)).isSome


/--
Run `x` with `maxHeartbeats` set to the lesser of `budget` and the ambient `maxHeartbeats`, treating
an ambient value of `0` ("unlimited") as larger than any `budget`. In either case `x` runs under
`withCurrHeartbeats`, so it gets a fresh allowance of that many heartbeats rather than whatever is
left of the ambient one.

If a runtime (or other non-interrupt) exception occurs while running `x`, it is caught and `dflt`
("default") is returned.

If `budget` is `0`, runs `x` directly without any restrictions or exception handling.

---
**Examples**

```
-- ambient `maxHeartbeats 200_000`, i.e. `Core.Context.maxHeartbeats = 200_000_000`
withHeartbeatBudget 1_000 dflt x             -- `x` gets a fresh 1_000 heartbeats
withHeartbeatBudget 1_000_000_000_000 dflt x -- `x` gets a fresh 200_000_000 heartbeats
withHeartbeatBudget 0 dflt x                 -- `x` gets what is left of the ambient allowance
-- ambient `maxHeartbeats 0`
withHeartbeatBudget 1_000 dflt x             -- `x` gets a fresh 1_000 heartbeats
```
-/
/-
Set when a heartbeat budget is exhausted. Without it a truncated declaration is indistinguishable
from a declined one: both report no emissions. Cleared per declaration by the linter.
-/
public initialize budgetExhaustedRef : IO.Ref Bool ← IO.mkRef false


public def withHeartbeatBudget {α : Type} (budget : Nat) (dflt : α) (x : TermElabM α) :
    TermElabM α := do
  if budget == 0 then return ← x
  let ambient := (← readThe Core.Context).maxHeartbeats
  let effectiveMax := if ambient == 0 then budget else min budget ambient
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxHeartbeats := effectiveMax })
      -- `withCurrHeartbeats` resets the heartbeat budget. #TODO
      (withCurrHeartbeats x))
    (fun _ => do budgetExhaustedRef.set true; pure dflt)

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
  -- `TargetedBinder.className` is the name of the _class_, i.e., for `[inst : Monoid M]`, it would
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
      let some W ← weakenedStatementType? const ws | return none
      -- `W` must actually be more general; neither gate below checks that (see
      -- `weakenedImpliesOriginal`).
      if cfg.generalityGuard then
        unless ← weakenedImpliesOriginal W const.type do return none
      -- a weakened `instance` must still admit as one, or the printed edit does not compile
      unless ← stillAdmissibleInstance const.name W const.levelParams do return none
      -- Compute weakening grade.
      let bodyG := (← recompiledAgainst? W src const.levelParams).isSome
      if !bodyG then
        if !accepted.isEmpty then return none
        unless ← weakeningHolds const candidate do return none
      let conclG ← match src.concl? with
        | some concl' => conclSourceIntact W concl' const.levelParams
        | none => pure false
      let bindersG := match binderNames[candidate.binder.idx]? with
        | some n => !src.binders.isEmpty && !bindersMention src.binders n
        | none => false
      return some {
        candidate,
        grade := .holds { binders := bindersG, concl := conclG, body := bodyG }
      }
    if let some g := g? then
      accepted := ws
      graded := graded.push g
  return graded
