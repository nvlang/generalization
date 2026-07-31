/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
module

public import Lean.Linter.Basic
import Mathlib.Lean.Elab.InfoTree

import GeneralizationLinter.Graph.GraphCache
import GeneralizationLinter.Analysis.Options
import GeneralizationLinter.Analysis.Replay
import GeneralizationLinter.Analysis.ReSynth
import GeneralizationLinter.Analysis.Verify

open Lean Meta Elab Command Linter Term
open GeneralizationLinter

namespace GeneralizationLinter.Frontend

/-!
# Linter

Suppose a file contains the following commands:

```
set_option A true in
open B in
set_option C true in
lemma something ‹binders› : ‹concl› := ‹value›
```

1.  Every top-level command of the file gets parsed into its own syntax tree `stx : Syntax`. In our
    example, we pretend that the file contains nothing else other than the four lines shown above,
    which would mean that there is only one top-level command.

    ```markdown
    `Command.in`
    ├─ [0] `Command.set_option`
    │      └─ … (4 children)
    ├─ [1] `atom "in"`
    └─ [2] `Command.in`
           └─ … (3 children)
    ```

    Note that `stx[2]` corresponds to the syntax tree of all but the first line of code. Also note
    that `stx` itself is just the `Syntax.node` corresponding to the root node of the tree.
    `Syntax.node` is defined as one of the possible values of the inductive type `Syntax`, and each
    `Syntax.node` comes with arguments `info : SourceInfo`, `kind : SyntaxNodeKind`, and `args :
    Array Syntax` (the node's children).

2.  Lean calls `elabCommandTopLevel stx`, which, for our purposes, we can understand as calling
    `elabCommand stx` first, and then `runLintersAsync stx` (many details are omitted here):

    1.  `elabCommand stx`: Since `stx.getKind != nullKind`, `elabCommand` calls `expandMacroImpl?`
        to check if there is a macro expander defined for `stx`'s kind, and finds `expandInCmd`. It
        then runs `expandInCmd stx` to get `stxNew`:

        ```markdown
        `null`
        ├─ [0] `Command.section`
        │      └─ … (3 children)
        ├─ [1] `Command.set_option`
        │      └─ … (4 children)
        ├─ [2] `Command.InternalSyntax.end_local_scope`
        │      └─ … (2 children)
        ├─ [3] `Command.in`
        │      └─ … (3 children)
        └─ [4] `Command.end`
              └─ … (2 children)
        ```

        `stxNew` would correspond to the following source code (written in diff notation to
        highlight the changes):

        ```diff
        - set_option A true in
        + section
        + set_option A true
        + end_local_scope 1
        open B in
        set_option C true in
        lemma something ‹binders› : ‹concl› := ‹value›
        + end
        ```

        Note that `stxNew[3] = stx[2]` remains unexpanded; expansion is performed one layer at a
        time. After expanding `stx` to `stxNew`, `elabCommand` calls `elabCommand stxNew`.

        1.  `elabCommand stxNew`: Since `stxNew.getKind == nullKind`, `elabCommand` calls
            `stxNew.getArgs.forM elabCommand`. And so on. When `elabCommand` is called on a node for
            which a specialized elaborator exists, it will call that specialized elaborator. For the
            node kinds seen above, these specialized elaborators are `elabSection`, `elabSetOption`,
            `elabEndLocalScope`, and `elabEnd` (`Command.in` has no elaborator, but rather just the
            macro expander `expandInCmd`). The full tree of `stxNew` requires many more specialized
            elaborators still.

    2.  `runLintersAsync stx`: By the time this call runs, `stx` has been fully processed by the
        elaborator and macro expander, which may have well modified the command state; in our
        example, we find that ``Command.State.env.constants.map₂[`something]`` now exists, and
        contains the `ConstantInfo` corresponding to the (fully elaborated) constant `something`
        that we declared. Nonetheless, `stx` still refers to the original syntax tree that the
        parser returned at the very beginning.

So `linter` has access to the syntax tree of the user's source code pre-elaboration (and thus also
pre-expansion), while the command state within which `linter` runs also provides it with access to
the fully elaborated declaration.

## Main definitions

* `linter`: This is the structure that gets registered via `initialize addLinter linter`, and whose
  `linter.run` function runs for every top-level command.
* `lintTypeclassesFor`: The function that computes, verifies, and emits the typeclass weakening
  suggestions.
-/

/--
Returns true if `type` has ≥1 binders that are targeted by the typeclass linter (under the given
configuration).
-/
def hasTargetedClassBinder (type : Expr) : MetaM Bool := do
  let implicit := generalizeTypeclasses.targetImplicit.get (← getOptions)
  forallTelescope type fun args _ => do
    for arg in args do
      let ld ← arg.fvarId!.getDecl
      let targeted := ld.binderInfo.isInstImplicit ||
        (implicit && ld.binderInfo matches .implicit | .strictImplicit)
      if targeted && (← isClass? ld.type).isSome then return true
    return false


/--
Given a weakening candidate `candidate` for a declaration with constant info `const`, returns a pair
of strings, the first string indicating what the existing binder looks like (e.g., `[Group G]`), and
the second string indicating the class application to which said binder may be weakened (e.g.,
`Monoid G`).
-/
def describeCandidate (const : ConstantInfo) (candidate : Candidate) : MetaM (String × String) :=
  targetedBinderTelescope const.type fun lds _ => do
    let old? := lds[candidate.binder.idx]?
    -- Targeted binder (unbracketed)
    let dispUnbracketed ← match old? with
      | some ld => pure (toString (← Meta.ppExpr ld.type))
      -- ↓ Should be unreachable.
      | none => pure (
          if candidate.binder.origName.isAnonymous then s!"⟨binder {candidate.binder.idx}⟩"
          else toString candidate.binder.origName)
    -- Targeted binder (bracketed)
    let disp := match candidate.binder.binderInfo with
      | .strictImplicit => s!"⦃{dispUnbracketed}⦄"
      | .implicit => "{" ++ dispUnbracketed ++ "}"
      | _ => s!"[{dispUnbracketed}]"
    -- Render a
    let render (t : Vertex) : MetaM String := do
      let some ld := old? | return toString t.name
      let some e ← replaceBinderType ld.type t | return toString t.name
      return toString (← Meta.ppExpr e)
    let target ← match candidate.shape with
      | .drop => pure "removed (dropped)"
      | .weaken weakerVertex => pure s!"weakened to `{← render weakerVertex}`"
      | .split weakerVertices => pure ("split into " ++
          ", ".intercalate (← weakerVertices.toList.mapM fun t => return s!"`{← render t}`"))
    return (disp, target)


/-- Run `x` with options `opts` added to the context, and catch runtime exceptions. -/
def withEffectiveContext (opts : Options) (heartbeats : Nat) (x : TermElabM Unit) :
    TermElabM Unit :=
  withOptions (fun _ => opts) <|
    withTheReader Core.Context (fun c => { c with maxHeartbeats := heartbeats }) <|
      tryCatchRuntimeEx x (fun _ => pure ())


/-- Returns `CommandElabM`'s options with the `set_option` wrappers in `wrappers` applied. -/
def wrapperEffectiveOptions? (wrappers : Array Syntax) :
    CommandElabM (Option Options) := do
  -- `elabSetOption` modifies infotrees of `CommandElabM`, so we snapshot `InfoState` here and roll
  -- back to it after setting the options.
  let savedInfo ← getInfoState
  let effectiveOpts ← foldSetOptionWrappers? wrappers (← getOptions)
    -- Callback establishing how to apply the `set_option` wrapper `w` to `opts : Options`.
    fun opts w => try
        -- We want to accumulate towards an `opts'` map that contains all prior `set_option`
        -- wrappers in `wrappers` already, on top of whatever options `CommandElabM` had before.
        let (opts', _) ← withScope
          -- `scope` is the (currently active) scope of `CommandElabM`, and `{ scope with opts }` is
          -- just that scope with `opts` applied to it, which is precisely the transient scope with
          -- which we want to run `elabSetOption`.
          (fun scope => { scope with opts })
          (elabSetOption
              (w.getArg 1)  -- option identifier
              (w.getArg 3)) -- option value
        pure (some opts')   -- return `opts` with `w` applied to it.
      catch _ => pure none
  -- Roll back `InfoState` so that modifications by `elabSetOption` don't mess with it.
  setInfoState savedInfo
  return effectiveOpts


private inductive Stats.Outcome
  | noGraph
  | untargeted
  | aborted
  | analyzed


private def Stats.Outcome.toJson : Stats.Outcome → Json
  | .noGraph => "noGraph"
  | .untargeted => "untargeted"
  | .aborted => "aborted"
  | .analyzed => "analyzed"


private def statsOfGraded (gw : GradedWeakening) : Json :=
  let c := gw.candidate
  let shape := match c.shape with
    | .drop => "drop" | .weaken _ => "weaken" | .split _ => "split"
  let grade := match gw.grade with
    | .holds p => s!"holds: {p.binders} {p.concl} {p.body}"
    | .unverified => "unverified"
  Json.mkObj [
    ("binder", toJson (toString c.binder.origName)),
    ("idx", toJson c.binder.idx),
    ("shape", toJson shape),
    ("targets", toJson (c.replacements.map fun v => toString v.name)),
    ("grade", toJson grade)
  ]


/--
Run the typeclass linter on the declaration named `declName` whose `ConstantInfo` is `const` and
whose syntax is described by `src`.
-/
def lintTypeclassesFor (cfg : LinterConfig) (graph : ClassGraph) (const : ConstantInfo)
    (src : DeclSource) (declName : Name)
    (omitCaveat : Bool := false) : TermElabM (Array GradedWeakening) := do
  let caveat := if omitCaveat then
    " This declaration's scope has one or more variables omitted from it, which means that the \
      suggested weakening may require the declaration or its value to be modified, or the omit \
      command to be removed, to be valid." else ""
  let gws ← gradedWeakenings cfg graph const src
  for gw in gws do
    let c := gw.candidate
    let (disp, target) ← describeCandidate const c
    let msg := match gw.grade with
      | .holds { binders, body, concl } =>
        let must := (if !concl then ["its conclusion"] else []) ++
          (if !body then ["its proof"] else [])
        let mustPart := if must.isEmpty then "" else
          s!", but {" and ".intercalate must} would have to be modified"
        let mightPart := if binders then "" else
          if must.isEmpty then ", but its binders might have to be modified"
          else ", and its binders might have to be as well"
        m!"the `{disp}` hypothesis of `{declName}` can be \
          {target}{mustPart}{mightPart}.{caveat}"
      -- For experiments only.
      | .unverified =>
        m!"[UNVERIFIED] the `{disp}` hypothesis of `{declName}` can be {target}."
    logLint linter.generalizeTypeclasses (← getRef) msg
  return gws


/--
This is the structure that gets registered via `initialize addLinter linter`, and whose `linter.run`
function runs for every top-level command.

For each command that `linter.run` is called on, it figures out whether it should run
`lintTypeclassesFor` and, if so, sets up the `DeclSource` record that they'll need and builds (or
fetches from cache) the typeclass graph.
-/
public def generalizeTypeclasses : Linter where
  -- `withSetOptionIn` peels off leading `set_option … in` commands. However, in our docstring
  -- example, it would only peel off `set_option A true in`, and not `set_option C true in`, because
  -- of the `open B in` between them. So `peelWrappers?` still needs to handle `set_option`s as
  -- well.
  run := withSetOptionIn fun cmd => do
    -- `declCmd` is `cmd` with all the leading `set_option … in`, `open … in`, `omit … in`, and
    -- `include … in` removed; see `peelWrappers?`.
    let some (wrappers, declCmd) := peelWrappers? cmd | return
    let some effectiveOpts ← wrapperEffectiveOptions? wrappers | return
    let lintOpts ← Command.withScope (fun s => { s with opts := effectiveOpts }) getLinterOptions
    -- Is the typeclass linter on?
    let tcOn := getLinterValue linter.generalizeTypeclasses lintOpts
    unless tcOn do return
    let sectionBinders := (← getScope).varDecls.map (·.raw)
    let omitTouched := hasOmitWrapper cmd || !(← getScope).omittedVars.isEmpty
    let acceptOmits := generalizeTypeclasses.acceptOmits.get effectiveOpts
    let declVals := declValNodes declCmd
    let tcSuppressed := (omitTouched && !acceptOmits) ||
      (declVals.size == 1 && hasUnreadDeclVal declVals[0]!)
    let hb := Core.getMaxHeartbeats effectiveOpts
    let cfg := linterConfigOfOptions effectiveOpts
    let declVals := declValNodes declCmd
    for infoTree in ← getInfoTrees do
      -- Theorem to lint.
      let thms := infoTree.getTheorems (← getEnv)
      unless thms.isEmpty do liftTermElabM <| withEffectiveContext effectiveOpts hb do
        -- Get body `Syntax` _without_ wrappers.
        let some rawBody ← (
            -- Because `linter.run` is called once for each top-level command, if `thms.length ≥ 2`,
            -- this means that we're dealing with a `mutual` block or a macro expanding to several
            -- theorems (note that this does not include declarations with the `@[to_additive]`
            -- attribute, because the automatic transportation it does happens at a later stage of
            -- elaboration, during which the linter no longer runs). #TODO: Make sure this is
            -- accurate.
            if declVals.size == 1 && thms.length == 1 then
              bodyTermOfDeclVal? declVals[0]!
            else pure none) | return
        let bodyStx := rewrapTerm wrappers rawBody
        let declSig? := declCmd.find? (·.isOfKind ``Parser.Command.declSig)
        let conclStx := declSig?.bind fun declSig' =>
          if declSig'[1].isOfKind ``Parser.Term.typeSpec then some (rewrapTerm wrappers declSig'[1][1])
          else none
        let src : DeclSource := {
          body := bodyStx,
          concl? := conclStx,
          binders := (declSig?.map (·[0].getArgs)).getD #[] ++ sectionBinders
        }
        -- Build class graph (or fetch it from cache).
        let graph? ← if tcOn && !tcSuppressed then
            tryCatchRuntimeEx (some <$> cachedClassGraph) (fun _ => pure none)
          else pure none
        for thm in thms do
          let const ← getConstInfo thm.name
          -- Skip `where`/`let rec` helpers that `getTheorems` may report.
          unless declIdMatches declCmd thm.name do continue
          -- Stats
          let statsOn := generalizationLinter.stats.get (← getOptions)
          let h0 ← IO.getNumHeartbeats
          let (outcome, emits) : Stats.Outcome × Array Json ←
            if let some graph := graph? then
              tryCatchRuntimeEx (
                  do
                    if ← hasTargetedClassBinder const.type then
                      let gws ← lintTypeclassesFor cfg graph const src thm.name
                        (omitCaveat := omitTouched)
                      return (.analyzed, if statsOn then gws.map statsOfGraded else #[])
                    else return (.untargeted, #[])
                ) (
                  fun _ => pure (.aborted, #[])
                )
              else (pure (.noGraph, #[]))
            if statsOn then
              let hb := (← IO.getNumHeartbeats) - h0
              logInfo m!"GL_STATS {(Json.mkObj [
                ("decl", toJson (toString thm.name)),
                ("heartbeats", toJson hb),
                ("outcome", outcome.toJson),
                ("suppressed", toJson tcSuppressed),
                ("emits", Json.arr emits)]).compress}"


initialize addLinter generalizeTypeclasses
