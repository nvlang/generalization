/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
module

public import GeneralizationLinter.Core.Verify
public import Lean.Elab.Term

open Lean Meta Elab Term

namespace GeneralizationLinter

/-!
# Recompile

This module concerns itself with elaborating a weakened term (usually the proof term of a theorem)
and type-checking the result against some expected type (usually the conclusion of a theorem). This
is used to verify a weakening candidate before it is ever suggested. The goal is to never emit a
single false positive, i.e., an erroneous suggestion.
-/

public structure SourceIntact where
  /-- Whether the declaration's binders _might_ have to be modified after applying the weakening. -/
  binders : Bool
  /-- Whether the declaration's conclusion has to be modified after applying the weakening. -/
  concl : Bool
  /--
  Whether the declaration's body (i.e., value) has to be modified after applying the weakening.
  -/
  body : Bool
deriving Inhabited, BEq

public def SourceIntact.all (si : SourceIntact) : Bool := si.binders && si.concl && si.body

/--
Some weakenings may be genuine weakenings, but require modifications in the value's (i.e., proof
term's) source code. We "grade" these weakenings as `needsModification`. We grade weakenings that
don't require any such modification as `.statementAndValueIntact`.
-/
public inductive WeakeningGrade where
  | holds (parts : SourceIntact)
  | unverified -- For experimental ablation measurements.
deriving Inhabited, BEq

public inductive WrapperClassification where
  /--
  "Declaration wrappers" that we can and should "replay", because they may affect our linter's
  verdict. These are `open … in` and `set_option … in` commands.
  -/
  | replayable
  /--
  "Declaration wrappers" that we can ignore, because they don't affect our linter's verdict (in the
  case of `omit`, this assumes diamond coherence; see implementation notes below). These are
  `include … in` commands, and `omit … in` commands that don't contain any `Term.hole` or
  `Term.syntheticHole` within them.

  ---
  **Implementation notes**

  `omit`s with holes are tricky for us. Consider the following example:

  ```
  variable {α β : Type} [Group α] [Inv β]

  omit [Inv _] in -- or section-wide `omit [Inv _]`
  theorem foo (a : α) : a⁻¹ = a⁻¹ := rfl
  ```

  If we treated `omit`s with holes like any other `omit`s and just ignored them, the linter would
  suggest the weakening `[Group α] ↝ [Inv α]` for `foo`. If the user then went ahead and applied
  that weakening without removing the `omit`, they'd get an error. For our purposes, this means that
  the weakening would be a false positive.

  Given that Mathlib, as of v4.32.1, doesn't have a single `omit` declaration with a hole, skipping
  declarations that do doesn't cost us any recall, while removing this "attack vector".

  We still need to show why "hole-less" `omit … in …` and `omit …` (section-wide) are fine, however.

  The argument relies on the assumption of diamond coherence. To see why it needs the assumption,
  consider the following example:

  ```
  variable {α : Type} [inst₁ : Group α] [inst₂ : Inv α]

  omit [Inv α] in -- or `omit [Inv α]`
  theorem foo (a : α) :
    @Inv.inv α (@DivInvMonoid.toInv α (@Group.toDivInvMonoid α inst₁)) a =
    @Inv.inv α (@DivInvMonoid.toInv α (@Group.toDivInvMonoid α inst₁)) a := rfl
  ```

  A few observations here:
  * The explicit `@…` transformations are important here: `theorem foo (a : α) : a⁻¹ = a⁻¹ := rfl`
    would emit the error `` cannot omit referenced section variable `inst₂` ``. That's because,
    without the `omit`, `foo` would just use `inst₂` instead of `inst₁`, as it prefers not having to
    call a bunch of projections.
  * Diamond coherence is violated here, as both `inst₁` and `inst₂` share the data-carrying
    descendant `Inv α`.
  * The linter would suggest weakening `[inst₁ : Group α]` to `[inst₁ : Inv α]`, with the caveat
    that the weakening would require `foo`'s statement to be modified (it'd have to replace the two
    `@Inv.inv α (@DivInvMonoid.toInv α (@Group.toDivInvMonoid α inst₁))` with `inst₁` after the
    weakening).

  A hole-free `omit [SomeClass a₁ … aₙ]` pins all its explicit arguments `a₁`, …, `aₙ`. For a
  weakening suggestion to clash with `[SomeClass a₁ … aₙ]`, we would need to have that

  2.  Fact: The linter will never introduce new names. Combined with the fact that the omitted names
      cannot be in the given declaration's scope, this implies that the suggested weakening can't
      intersect/clash with the omitted names.
  -/
  | ignorable
  /--
  "Declaration wrappers" that we cannot replay, and which may affect our linter's verdict. When a
  declaration is wrapped with one or more of these kinds of wrappers, we skip it. Any wrappers that
  are not `.replayable` or `.ignorable` are treated as `.refused`.
  -/
  | refused
deriving Inhabited, BEq

/--
`lemma` is a Mathlib macro that the elaborator expands to `theorem`. However, pre-elaboration, its
`SyntaxNodeKind` is `` `lemma ``, while the pre-elaboration `SyntaxNodeKind` of all other
declarations that the linter may analize is `Parser.Command.declaration`.
-/
public def lemmaKind : SyntaxNodeKind := `lemma

/-- Classify "wrappers". -/
public def classifyWrapper (w: Syntax) : WrapperClassification :=
  match w.getKind with
  | ``Parser.Command.open | ``Parser.Command.set_option => .replayable
  | ``Parser.Command.include | ``Parser.Command.omit => .ignorable
  | _ => .refused

public partial def hasOmitWrapper (stx : Syntax) : Bool :=
  if stx.getKind != ``Parser.Command.in then false
  else (stx.getArg 0).getKind == ``Parser.Command.omit || hasOmitWrapper (stx.getArg 2)

/--
Peel any `open … in`, `set_option … in`, and "hole-less" `omit … in …` "wrappers" off of the main
declaration. For example, if `stx` was

```
open Nat in
set_option pp.all true in
omit [Monoid M] in
@[instance] theorem something : … := …
```

then calling `peelWrappers? stx` would return `some (#[‹open Nat›, ‹set_option pp.all›],
‹@[instance] lemma something : … := …›)`. (Note that the `omit [Monoid M] in` wrapper is not among
those returned; this is because we can safely ignore it. See `WrapperClassification.ignorable` for
more information.)

If the declaration includes any other wrappers (`omit … in …` with holes, `attribute … in …`,
`include … in …`, etc.), return `none`. This is because `peelWrappers?`'s output is passed on to
`rewrapTerm` to get rewrapped into a _term_ instead of a command or declaration (which would be much
harder to deal with further down the line), and only `open` and `set_option` are the only wrappers
of this kind that are available in `Parser.Command.Term`.

There's <2000 declarations in Mathlib v4.32.0 that use wrappers that lead `peelWrappers?` to return
`none` (which in turn prevents the linter from being able to emit any suggestions).

---
**Example**

Suppose we have the following declaration:

```
open Nat in
@[instance] theorem t : True := trivial
```

The corresponding `Syntax` tree is:

```markdown
`Lean.Parser.Command.in`
├─ `Lean.Parser.Command.open`                             ─┐
│  ├─ `atom "open"`                                        │ `wrappers[0]`
│  └─ `Lean.Parser.Command.openSimple`                     │
│     └─ `null` (many1 ident)                              │
│        └─ `ident Nat`                                   ─┘
├─ `atom "in"`
└─ `Lean.Parser.Command.declaration`                      ─┐
   ├─ `Lean.Parser.Command.declModifiers`                  │ `decl`
   │  ├─ `null` (optional docComment)                      │
   │  ├─ `null` (optional attributes)                      │
   │  │  └─ `Lean.Parser.Term.attributes`                  │
   │  │     ├─ `atom "@["`                                 │
   │  │     ├─ `null` (sepBy1 attrInstance)                │
   │  │     │  └─ `Lean.Parser.Term.attrInstance`          │
   │  │     │     ├─ `Lean.Parser.Term.attrKind`           │
   │  │     │     │  └─ `null` (optional scoped / local)   │
   │  │     │     └─ `Lean.Parser.Attr.instance`           │
   │  │     │        ├─ `atom "instance"`                  │
   │  │     │        └─ `null` (optional priority)         │
   │  │     └─ `atom "]"`                                  │
   │  ├─ `null` (optional visibility)                      │
   │  ├─ `null` (optional protected)                       │
   │  ├─ `null` (optional meta / noncomputable)            │
   │  ├─ `null` (optional unsafe)                          │
   │  └─ `null` (optional partial / nonrec)                │
   └─ `Lean.Parser.Command.theorem`                        │
      ├─ `atom "theorem"`                                  │
      ├─ `Lean.Parser.Command.declId`                      │
      │  ├─ `ident t`                                      │
      │  └─ `null` (optional universe binders)             │
      ├─ `Lean.Parser.Command.declSig`                     │
      │  ├─ `null` (many binder)                           │
      │  └─ `Lean.Parser.Term.typeSpec`                    │
      │     ├─ `atom ":"`                                  │
      │     └─ `ident True`                                │
      └─ `Lean.Parser.Command.declValSimple`               │
         ├─ `atom ":="`                                    │
         ├─ `ident trivial`                                │
         ├─ `Lean.Parser.Termination.suffix`               │
         │  ├─ `null` (optional terminationBy / fixpoint)  │
         │  └─ `null` (optional decreasingBy)              │
         └─ `null` (optional whereDecls)                  ─┘
```

(See Lean/Parser/Command.lean, Lean/Parser/Term.lean, and Lean/Parser/Attr.lean for more information
on the parentheticals in the tree above.)

So `peelWrappers` would return `some (wrappers, decl)`, where `wrappers` and `decl` are as indicated
above.
-/
public partial def peelWrappers? (stx : Syntax) (wrappers : Array Syntax := #[]) :
    Option ((Array Syntax) × Syntax) :=
  if stx.getKind == ``Parser.Command.declaration || stx.getKind == lemmaKind then
    some (wrappers, stx)
  else if stx.getKind == ``Parser.Command.in then
    let w := stx.getArg 0
    match classifyWrapper w with
    | .replayable => peelWrappers? (stx.getArg 2) (wrappers.push w)
    | .ignorable => peelWrappers? (stx.getArg 2) wrappers
    | .refused => none
  else none

/--
Given the syntax tree `declVal` of a declaration, return the value as a term syntax tree. In the
case of theorems, this value corresponds to the proof term.

---
**Implementation notes**

Argument positions of relevant `SyntaxNodeKind` can be seen in the following code block, adapted by
us from code from `Lean/Parser/Command.lean`:

```
def declValSimple    := leading_parser
  " :=" >>                      -- dval[0]
  ppHardLineUnlessUngrouped >>  -- pretty-printer stuff
  declBody >>                   -- dval[1]
  Termination.suffix >>         -- dval[2]
  optional Term.whereDecls      -- dval[3]

def whereStructInst  := leading_parser
  ppIndent ppSpace >>       -- pretty-printer stuff
  "where" >>                -- dval[0]
  -- ↓ dval[1]
  Term.structInstFields (sepByIndent Term.structInstField "; " (allowTrailingSep := true)) >>
  optional Term.whereDecls  -- dval[2]
```

---
**Example**

For the example from `peelWrappers?`, `bodyTermOfDeclVal?` returns the following syntax tree:

```markdown
`ident trivial`
```
-/
public def bodyTermOfDeclVal? (dval : Syntax) (wrapped : Bool) : TermElabM (Option Syntax) := do
  if dval.getKind == ``Parser.Command.declValSimple then
    return some dval[1]
  else if dval.getKind == ``Parser.Command.whereStructInst then
    -- We don't support wrapped structs, because (#TODO: why?).
    if wrapped then return none
    -- Reprint struct, then parse the result.
    match Parser.runParserCategory (← getEnv) `term
      ("{ " ++ (dval[1].reprint.getD "") ++ " }") with
    | .ok t => return some t
    | .error _ => return none
  else return none

/--

---
**Example**

Continuing the example from `peelWrappers?`, we have that `rewrapTerm` would combine the single
wrapper in `wrappers`

```markdown
`Lean.Parser.Command.open`
├─ `atom "open"`
└─ `Lean.Parser.Command.openSimple`
    └─ `null` (many1 ident)
      └─ `ident Nat`
```

with the `bodyTermOfDeclVal?` output `stx`

```markdown
`ident trivial`
```

into the `Syntax` tree

```markdown
`Lean.Parser.Term.open`
├─ `atom "open"`
├─ `Lean.Parser.Command.openSimple`
│  └─ `null` (many1 ident)
│     └─ `ident Nat`
├─ `atom "in"`
└─ `ident trivial`
```
-/
public def rewrapTerm (wrappers : Array Syntax) (stx : Syntax) : Syntax :=
  wrappers.foldr (init := stx) fun w body =>
    let kind := match w.getKind with
      | ``Parser.Command.open => ``Parser.Term.open
      | ``Parser.Command.set_option => ``Parser.Term.set_option
      -- Should be unreachable.
      | k => panic! s!"rewrapTerm: unexpected wrapper kind '{k}'\
          (peelWrappers? should only collect open/set_option)"
    mkNode kind (w.getArgs ++ #[mkAtom "in", body])

/--
Applies `set_option` wrappers to `init` using `elabOne` and returns the result.

---
**Implementation notes**

An `Options` value is essentially just a map: `Options.map : NameMap DataValue` from `Name` of
options (e.g., `` `pp.raw `` in `set_option pp.raw true`) to `DataValue`s (e.g., `ofBool true` in
`set_option pp.raw true`). `foldSetOptionWrappers?` just "applies" the `set_option` commands among
`wrappers` to `init : Options` using `elabOne` and returns the result, or `none` if `elabOne`
returned `none` at any point.
-/
public def foldSetOptionWrappers? {m : Type → Type} [Monad m] (wrappers : Array Syntax) (init : Options)
    (elabOne : Options → Syntax → m (Option Options)) : m (Option Options) := do
  let mut opts := init -- Accumulator of options
  -- For each `set_option` wrapper,
  for w in wrappers do
    if w.getKind == ``Parser.Command.set_option then
      match ← elabOne opts w with
      | some eopts => opts := eopts
      | none => return none
  return some opts

/-- Returns all child nodes of kind `kind`.  -/
public partial def collectNodes (kind : SyntaxNodeKind) : Syntax → Array Syntax
  | stx@(.node _ kind' args) =>
    let inner := args.flatMap (collectNodes kind)
    if kind' == kind then #[stx] ++ inner else inner
  | _ => #[]

/--
Returns the "value" nodes of `stx`, i.e., the `:= …` node (`Parser.Command.declValSimple`) and
optional `where …` node (`Parser.Command.whereStructInst`).

See implementation notes of `bodyTermOfDeclVal?` for more info.
-/
public def declValNodes (stx : Syntax) : Array Syntax :=
  collectNodes ``Parser.Command.declValSimple stx
    ++ collectNodes ``Parser.Command.whereStructInst stx

public def hasUnreadDeclVal (dval : Syntax) : Bool :=
  if dval.getKind == ``Parser.Command.declValSimple then
    !(dval[2].getArgs.all (·.isNone)) || !dval[3].isNone
  else if dval.getKind == ``Parser.Command.whereStructInst then
    !dval[2].isNone
  else false

public def declIdMatches (declCmd : Syntax) (declName : Name) : Bool :=
  match declCmd.find? (·.isOfKind ``Parser.Command.declId) with
  | some declId => (declId.getArg 0).getId.eraseMacroScopes.isSuffixOf declName
  | none => true


/-- Source code (`Syntax`) of a declaration and its value. -/
public structure DeclSource where
  body : Syntax
  concl? : Option Syntax := none
  binders : Array Syntax := #[]
deriving Inhabited

/--
Given a weakened declaration `W` of the form `‹binders› : concl` (where `concl` is the same as the
original declaration's), re-elaborate the declaration's value's source code (`bodyStx`, usually
corresponding to a proof term) into `val` and type-check that we have `val : concl`. Return `some
val` if successful, or `none` otherwise.
-/
public def recompiledAgainst? (W : Expr) (src : DeclSource) (levelNames : List Name := []) : TermElabM (Option Expr) :=
  suppressingDiagnostics do
  try withLevelNames ((← getLevelNames) ++ levelNames) do
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
      catch _ => return none
    if let some val ← attempt none then return some val
    let some conclStx := src.concl? | return none
    let depth? ← try
        Meta.forallTelescope W fun ys _ => do
          let c ← withoutErrToSorry (elabTermAndSynthesize conclStx none)
          let rec foralls : Expr → Nat
            | .forallE _ _ b _ => foralls b + 1
            | _ => 0
          let k := min (foralls c) ys.size
          return if k == 0 then none else some (ys.size - k)
      catch _ => pure none
    let some depth := depth? | return none
    attempt (some depth)
  catch _ => return none

public def conclSourceHolds (W : Expr) (conclStx : Syntax) (levelNames : List Name := []) :
    TermElabM Bool :=
  suppressingDiagnostics do
  try
    withLevelNames ((← getLevelNames) ++ levelNames) do
      Meta.forallTelescope W fun ys concl => do
        let newConcl ← withoutErrToSorry (elabTermAndSynthesize conclStx none)
        -- `forallTelescope W` strips every `∀` from `W`, even ones that may actually belong to the
        -- conclusion of `W`, which we don't want. So we consult `conclStx` and check how many
        -- leading `∀`s it has, and re-abstract precisely that number of the telescoped `W`'s
        -- trailing binders. #TODO
        let rec foralls : Expr → Nat
          | .forallE _ _ b _ => foralls b + 1
          | _ => 0
        let k := min (foralls newConcl) ys.size
        Meta.isDefEq newConcl (← Meta.mkForallFVars (ys.extract (ys.size - k) ys.size) concl)
    catch e =>
      -- We don't want a timeout here to lead to a claim that "the conclusion would have to be
      -- modified" (we don't know whether that's true or not at this point), but rather just to
      -- dropping the candidate altogether.
      if e.isRuntime then throw e else return false

/--
#TODO
-/
public def recompiledVal? (const : ConstantInfo) (src : DeclSource) (ws : Array (Nat × Array Vertex)) :
    TermElabM (Option (Expr × Expr)) := do
  let some W ← weakenedStatementType const ws | return none
  return (← recompiledAgainst? W src const.levelParams).map (W, ·)

/-- Wrapper around `recompiledVal?`; returns `true` iff #TODO -/
public def recompileHolds (const : ConstantInfo) (src : DeclSource) (ws : Array (Nat × Array Vertex)) :
    TermElabM Bool :=
  return (← recompiledVal? const src ws).isSome

/--
Does any of the declaration's binders, _as source code_ (`Syntax`), mention the binder `name`?

---
**Examples**

```
binderSourceNamesBinder ‹[inst : Ring R] [AddCommMonoid M] [Module R M]› `inst = false
```
-/
public def binderSourceNamesBinder (binders : Array Syntax) (name : Name) : Bool :=
  binders.any fun b =>
    let args := b.getArgs
    let searched := if args.size ≥ 3 then args.extract 2 args.size else args
    searched.any fun arg => (arg.find? fun s =>
      (s.isIdent && !name.hasMacroScopes && !name.isAnonymous &&
        s.getId.eraseMacroScopes.getRoot == name) ||
      (s.isIdent && s.getId == ``inferInstance) ||
      (match s with | .atom _ v => v == "‹" | _ => false)
    ).isSome

/--
If `budget < maxHeartbeats`, run `x` with `maxHeartbeats` lowered to `budget`. Otherwise, just
run `x` with the existing `maxHeartbeats`.
-/
-- Note: `dflt` stands for "default".
public def withHeartbeatBudget {α : Type} (budget : Nat) (dflt : α) (x : TermElabM α) :
    TermElabM α := do
  if budget == 0 then return ← x
  let ambient := (← readThe Core.Context).maxHeartbeats
  let effectiveMax := if ambient == 0 then budget else min budget ambient
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxHeartbeats := effectiveMax })
      (withCurrHeartbeats x))
    (fun _ => pure dflt)

public structure GradedWeakening where
  candidate : Candidate
  grade : WeakeningGrade
deriving Inhabited

/--
Given a declaration with constant into `const` and value source code `bodyStx` (as well as a linter
config and class graph), return an array of verified, graded weakenings that could be applied to the
declaration.
-/
public def gradedWeakenings (cfg : LinterConfig) (graph : ClassGraph) (const : ConstantInfo)
    (src : DeclSource) : TermElabM (Array GradedWeakening) := do

  let candidates ← withHeartbeatBudget cfg.perCandidateHeartbeats #[] (meetCandidates cfg graph const)
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
