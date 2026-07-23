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

public inductive WeakeningGrade where
  | proofIntact
  | needsModification
  | unverified -- For experimental ablation measurements.
deriving Inhabited, BEq

public inductive WrapperClassification where
  /--
  "Declaration wrappers" that we can and should "replay", because they may affect our linter's
  verdict. These are `open … in` and `set_option … in` commands.
  -/
  | replayable
  /--
  "Declaration wrappers" that we can ignore, because they don't affect our linter's verdict. These
  are `include … in` commands, and `omit … in` commands that don't contain any `Term.hole` or
  `Term.syntheticHole` within them. TODO: More details on why.
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

/--
Classify "wrappers"
-/
public def classifyWrapper (w: Syntax) : WrapperClassification :=
  match w.getKind with
  | ``Parser.Command.open | ``Parser.Command.set_option => .replayable
  | ``Parser.Command.include => .ignorable
  | ``Parser.Command.omit =>
    if (w.find? fun s => s.getKind == ``Parser.Term.hole
      || s.getKind == ``Parser.Term.syntheticHole).isSome
    then .refused else .ignorable
  | _ => .refused


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
‹@[instance] lemma something : … := …›)`. (Note that the `omit [Monoid M] in` wrapper is not
among those returned; this is because TODO)

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
      | _ => ``Parser.Term.set_option -- TODO: Should be unreachable, so make it fail loudly
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

-- public def declIdMatches (declCmd : Syntax) (declName : Name) : Bool :=
--   match declCmd.find? (·.isOfKind ``Parser.Command.declId) with
--   | some declId => (declId.getArg 0).getId.eraseMacroScopes.isSuffixOf declName
--   | none => false

/-- TODO -/
public def recompiledAgainst? (W : Expr) (bodyStx : Syntax) : TermElabM (Option Expr) :=
  suppressingDiagnostics do
  try
    Meta.forallTelescope W fun ys concl => do
      let val ← elabTermAndSynthesize bodyStx (some concl)
      unless ← Meta.isDefEq (← Meta.inferType val) concl do return none
      let val ← instantiateMVars (← Meta.mkLambdaFVars ys val)
      if val.hasSorry || val.hasExprMVar then return none
      discard <| Meta.check val
      return some val
  catch _ => return none

/-- TODO -/
public def recompiledVal? (const : ConstantInfo) (bodyStx : Syntax)
    (ws : Array (Nat × Array Key)) : TermElabM (Option (Expr × Expr)) := do
  let some W ← weakenedStatementType const ws | return none
  return (← recompiledAgainst? W bodyStx).map (W, ·)

/-- TODO -/
public def recompileHolds (const : ConstantInfo) (bodyStx : Syntax)
    (ws : Array (Nat × Array Key)) : TermElabM Bool :=
  return (← recompiledVal? const bodyStx ws).isSome

public structure GradedWeakening where
  candidate : Candidate
  grade : WeakeningGrade
  deriving Inhabited

/-- TODO -/
public def gradedWeakenings (cfg : LinterConfig) (graph : ClassGraph) (const : ConstantInfo)
    (bodyStx : Syntax) : TermElabM (Array GradedWeakening) := do
  (← meetCandidates cfg graph const).filterMapM fun candidate => do
    if !cfg.verify then
      return some { candidate, grade := .unverified }
    if ← recompileHolds const bodyStx #[(candidate.binder.idx, candidate.replacementKeys)] then
      return some { candidate, grade := .proofIntact}
    else if ← weakeningHolds const candidate then
      return some { candidate, grade := .needsModification }
    else
      return none
