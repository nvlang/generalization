/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
module

public import Lean.Elab.Term

open Lean Meta Elab Term

namespace GeneralizationLinter

/-! # Replay -/

public inductive WrapperClassification where
  /--
  "Declaration wrappers" that we can and should "replay", because they may affect our linter's
  verdict. These are `open … in` and `set_option … in` commands.
  -/
  | replayable
  /--
  "Declaration wrappers" that we can ignore, because they don't affect our linter's verdict (in the
  case of `omit`, it's merely that they are relatively unlikely to affect our linter's verdict "in
  spirit"; see implementation notes below).

  ---
  **Implementation notes**

  `omit`s are tricky for us, and can invalidate `gradedWeakenings`'s `SourceIntact` verdicts. The
  most common case is a suggested weakening being sensible but requiring some `omit` command(s)
  being adjusted. Ensure that `gradedWeakenings`'s `SourceIntact` verdicts remain accurate in such
  cases would require a significant amount of machinery, and `omit`s are relatively rare in Mathlib,
  so the compromise we made was to skip declarations wrapped in or affected by `omit`s by default,
  but provide the option `generalizationLinter.acceptOmits`, which, when set to `true`, will lint
  these same declarations as if there were no `omit`s at all. The idea is that the user is then
  aware of the caveat that `omit`s impose on suggestions' `SourceIntact` verdicts when `omit`s are
  involved.
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
declarations that the linter may analyze is `Parser.Command.declaration`.
-/
public def lemmaKind : SyntaxNodeKind := `lemma


/-- Classify "wrappers". -/
public def classifyWrapper (w: Syntax) : WrapperClassification :=
  match w.getKind with
  | ``Parser.Command.open | ``Parser.Command.set_option => .replayable
  | ``Parser.Command.include
  -- Note: when `acceptOmits` is `false` (default), then `omit`s are not actually treated as
  -- ignorable.
  | ``Parser.Command.omit => .ignorable
  | _ => .refused

public partial def hasOmitWrapper (stx : Syntax) : Bool :=
  if stx.getKind != ``Parser.Command.in then false
  else (stx.getArg 0).getKind == ``Parser.Command.omit || hasOmitWrapper (stx.getArg 2)

/--
Peel any `open … in`, `set_option … in`, `include … in …`, and `omit … in …` "wrappers" off of the
main declaration. For example, if `stx` was

```
open Nat in
set_option pp.all true in
omit [Monoid M] in
@[instance] lemma something : … := …
```

then calling `peelWrappers? stx` would return `some (#[‹open Nat›, ‹set_option pp.all›],
‹@[instance] lemma something : … := …›)`. (Note that the `omit [Monoid M] in` wrapper is not among
those returned; this is because we either ignore `omit`s entirely or, if `acceptOmits` is `false`
(which it is by default), declarations with `omit`s are skipped by the linter altogether.)

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

So `peelWrappers?` would return `some (wrappers, decl)`, where `wrappers` and `decl` are as
indicated above.
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

For `whereStructInst`, there's no curly brackets surrounding the structure fields, so there's no
direct way that we can extract the fields for re-elaboration. So, what we do instead is construct a
`Term.structInst` syntax tree which simply wraps the `Term.structInstFields` node from the `dval`
that we were handed with curly brackets. In essence, what we're doing is taking

```
theorem foo … : … where
  field₁
  ⋮
  fieldₙ
```

and constructing

```
{
  field₁,
  ⋮
  fieldₙ
}
```

so that we can hand this over for re-elaboration, so that we can check that the weakening doesn't
mess with any of the fields.

**Note:** Declarations like

```
theorem foo … : … := …
where
  field₁
  ⋮
  fieldₙ
```

get skipped for now. This is because, for these kinds of declarations, Lean elaborates each `fieldᵢ`
into a separate constant, so we'd have to check each of them recursively. This is certainly doable,
but we could only find 3 theorems or lemmas in Mathlib v4.32.1 that make use of `where` in this way
(`LucasLehmer.norm_num_ext.sModNatTR_eq_sModNat`, `TrivSqZeroExt.snd_pow_of_smul_comm`, and
`RingTheory.Sequence.IsWeaklyRegular.prototype_perm`), so we expect the impact to be relatively
small. Nonetheless, it's potential future work.

---
**Example**

For the example from `peelWrappers?`, `bodyTermOfDeclVal?` returns the following syntax tree:

```markdown
`ident trivial`
```
-/
public def bodyTermOfDeclVal? (dval : Syntax) : TermElabM (Option Syntax) := do
  if dval.getKind == ``Parser.Command.declValSimple then
    return some dval[1]
  else if dval.getKind == ``Parser.Command.whereStructInst then
    return some <| mkNode ``Parser.Term.structInst #[
      mkAtom "{",
      mkNullNode,
      dval[1], -- Parser.Term.structInstFields
      mkNode ``Parser.Term.optEllipsis #[],
      mkNullNode,
      mkAtom "}"
    ]
  -- We skip `Parser.Term.whereDecls`; see implementation notes.
  else return none


/--
Syntactically "rewrap" a term with the replayable previously peeled wrappers.

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
