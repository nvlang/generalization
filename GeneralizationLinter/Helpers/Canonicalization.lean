/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
module

public import Lean.Expr
public import Lean.Environment
public import Lean.Meta.Basic
public import GeneralizationLinter.Helpers.Vertex
import Lean.Meta.SynthInstance

open Lean Meta

namespace GeneralizationLinter

/-!
# Canonicalization

TODO: Module docstring.

**Note:** We try to use the terms "binder", and "value (passed to a function)",
and "argument" consistently, with the conventional understanding of the first
two terms (see below), and using the last term ("argument") as a stand-in for
"binder or value (passed to a function)".

```
def f (n : Nat) : Nat := n * n
      ^^^^^^^^^ binder
def x = f 123
          ^^^ value
```
-/

open Lean Meta GeneralizationLinter
open Std (HashMap)

/-! ## Head Helpers -/

/--
`isTypeConstructor e` is `true` iff `e` is a (possibly nullary) type constructor
constant.

---
**Examples**

`isTypeConstructor` returns `true` on the following:

* Nullary type constructors: `Nat`, etc.
* Unary type constructors: `Group`, `List`, etc.
* Binary type constructors: `Prod`, `And`, etc.
* etc.

`isTypeConstructor` returns `false` on the following:

* Constants that are not type constructors: `And.intro`, `Nat.succ`, etc.
* Things that are not constants: `3`, `#[3]`, `{}`, `[]`, etc.
-/
public def isTypeConstructor (env : Environment) (e : Expr) : Bool :=
  match e with
  | .const c _ => (env.find? c).any (·.type.getForallBody.isSort)
  | _          => false

/-! ## What to keep -/

/--
Returns `true` only if `fvar` is recoverable from `e`, i.e., only if `e` "pins" `fvar`. Here, `e :
Expr` is the type of a binder, stripped of gadgets (`outParam` & co.).

**Note:** If `false` is returned, it doesn't guarantee that `fvar` is _not_ recoverable.
-/
partial def recoverableFrom (fvar : FVarId) (e : Expr) : Bool :=
  match e with
  | .forallE _ binderType body _ => recoverableFrom fvar binderType || recoverableFrom fvar body
  | _ =>
    let fn := e.getAppFn
    if fn.isConst then
      e.getAppArgs.any fun arg => arg == .fvar fvar || recoverableFrom fvar arg
    else false -- the safe default

initialize keySlotsCacheRef : IO.Ref (HashMap Name (Array Bool)) ← IO.mkRef {}

/--
Given a head constant `head`, return a boolean mask `#[b₁ … bₙ]` (`bᵢ : Bool`) such that `bᵢ` is
`true` iff the `i`th slot of `head` is one that should be kept when converting an application of
`head` into a `Key`.

Explicit slots are always kept, instance implicit slots are always dropped, and implicit and strict
implicit slots are dropped only if their values are recoverable from the values of the kept slots.
-/
def keySlots (head : Name) : MetaM (Array Bool) := do
  if let some m := (← keySlotsCacheRef.get)[head]? then return m -- cache hit
  let some info := (← getEnv).find? head | return #[]
  let slots ← forallTelescope info.type fun params _ => do
    let decls ← params.mapM (·.fvarId!.getDecl)
    let binderInfos : Array BinderInfo := decls.map (·.binderInfo)
    -- binder types with gadgets (outParam & co.) removed.
    let binderTypes : Array Expr := decls.map (·.type.cleanupAnnotations)
    let mut keep : Array Bool := #[]
    for i in [0:params.size] do
      if binderInfos[i]!.isExplicit then
        keep := keep.push true -- explicit params are always kept
      else if binderInfos[i]!.isInstImplicit then
        keep := keep.push false -- instance implicit params are always dropped
      else
        -- implicit or strict implicit params: drop only if recoverable from the
        -- type of a non-instance-implicit binder that follows it in the telescope.
        let fvar := params[i]!.fvarId!
        let recoverable := (List.range params.size).any fun j =>
          j > i && !binderInfos[j]!.isInstImplicit && recoverableFrom fvar binderTypes[j]!
        keep := keep.push !recoverable -- keep params that we're not sure are recoverable
    return keep
  keySlotsCacheRef.modify (·.insert head slots) -- cache result
  return slots

/--
The ***key arguments*** of an application `fn a₁ … aₙ` (`vals = #[a₁, …, aₙ]`), in accordance with
`keySlots fn`.
-/
def keyArgs (fn : Expr) (vals : Array Expr) : MetaM (Array Expr) := do
  let slots ← match fn.constName? with
    | some head => keySlots head
    | none => pure #[] -- non-const head ⟹ keep all vals
  pure <| vals.zipIdx.filterMap fun (val, i) =>
    if slots[i]?.getD true then some val else none -- keep by default

/--
Used to strip the universe-level arguments off the heads of type formers used within a key slot. We
delegate all handling of universe levels to `Vertex.levels`.
-/
public def eraseHeadLevels : Expr → Expr
  | .const c _ => .const c []
  | e => e

/--
Retrieves the value of a `Nat`-valued argument.

---
**Examples**

* `.lit (.natVal n)` → `n`
* `@OfNat.ofNat ℕ n _` → `n`
-/
public def natLitOf? : Expr → Option Nat
  | .lit (.natVal n) => some n
  | e => match e.getAppFnArgs with
    | (``OfNat.ofNat, #[ty, .lit (.natVal n), _]) =>
      if ty.isConstOf ``Nat then some n else none
    | _ => none

/-! ## Anti-Unification -/

/--
As we walk an `Expr` (generally, a telescope), this monad helps us keep track of
two things:

* `HashMap FVarId Nat`: For each `fvar id` (where `id` is some `FVarId`) we
  encounter in the expression we're parsing, we add an entry `id → k` to this
  map to note to which canonical `bvar k` we've mapped `fvar id`.
* `Array Expr`: This keeps track of the specific carriers we've collected thus
  far, ordered by their de Bruijn indices.

**Invariant:** The size of the Array is always greater than or equal to the size
of the HashMap.
-/
public abbrev CanonVarsM := StateT ((HashMap FVarId Nat) × (Array Expr)) MetaM

/--
Canonicalize a single binder/argument.

---
**Examples**

* `ℕ` → `ℕ`
* `3` → `3`
* Applied over the arguments of `Group G` → `Group #0`
* Applied over the arguments of `Module R R` → `Module #0 #0`
* Applied over the arguments of `Pow α ℕ` → `Pow #0 ℕ`
* Applied over the arguments of `OfNat α 1` → `OfNat #0 1`
-/
public partial def canonArg (e : Expr) : CanonVarsM Expr := do
  let e ← whnfR e.consumeMData -- strip annotations and reduce to WHNF
  match e with
  | .fvar id => -- fvars get their index canonicalized
    let (m, carriers) ← get -- get state from CanonVarsM
    match m[id]? with
    | some k => return .bvar k -- we've seen this fvar before
    | none   => -- new fvar
      let k := carriers.size
      set (m.insert id k, carriers.push e) -- update CanonVarsM state
      return .bvar k
  | _ =>
    if let some n := natLitOf? e then return mkRawNatLit n -- nat literals are kept as-is
    let fn := e.getAppFn
    if isTypeConstructor (← getEnv) fn then
      -- If `e` is "f a₁ … aₙ", with "f" a type constructor, then
      -- canonicalize "a₁ … aₙ" to "a₁' … aₙ'" and return "f a₁' … aₙ'".
      -- Note that "f" may be a nullary type constructor, e.g., `Nat`.
      let kept ← keyArgs fn e.getAppArgs
      return mkAppN (eraseHeadLevels fn) (← kept.mapM canonArg)
    else
      -- `e` is not function app, or "f" is not a type constructor. In this case, we abstract `e` to
      -- a fresh bvar, and record `e` so that `reify` can recover it later on.
      let (m, carriers) ← get
      let k := carriers.size
      set (m, carriers.push e)
      return .bvar k

/--
Canonicalized universe arguments for a head with universe arguments `lvls`.

* `concrete`: when there are no universe parameters or metavariables; in other
  words, when the class application is not universe-polymorphic. In this case,
  we track the specific universe levels of the class application.
* `polymorphic`: when the class application is universe-polymorphic. In this case, we
  don't track the universe levels, so we "erase" that information.

---
**Examples**

```
universeLevelsOf [0, 1] = concrete #[0, 1]
universeLevelsOf [u]    = polymorphic      -- `u` is a universe variable
universeLevelsOf []     = concrete #[]     -- monomorphic class, e.g., `Std.Refl`
```
-/
public def universeLevelsOf (lvls : List Level) : UniverseLevels :=
  if lvls.all (fun l => !l.hasParam && !l.hasMVar) then
    .concrete ((lvls.map (·.normalize)).toArray)
  else .polymorphic


/--
Given an `Expr` of a class application, canonicalize it into a `Key`.

---
**Implementation notes**

* The head name (which sets `Vertex.name`) and canonicalized arguments (which set `Vertex.pattern`)
  are taken from the `whnfR` form of the expression, so for example `IsNoetherianRing R`, which
  reduces to `IsNoetherian R R`, would have ```Vertex.name := ``IsNoetherian``` and `Vertex.pattern
  := #[#0, #0]`.
* For a family class binder like `∀ prefix, C args`, the body (`C args`) determines the `Vertex`
  fields, while the prefix is used to abstract the

  TODO: finish this docstring

---
**Precondition**

* `Expr` must be a class application. It should've been extracted from an instance implicit binder
  of a theorem/lemma.
-/
public def toKey (e: Expr) : MetaM Key := do
  let e0 := e.consumeMData
  if (← whnfR e0).isForall then
    forallTelescopeReducing e0 fun prefixes body => do
      let app ← plainKey (body.consumeMData)
      if app.name == .anonymous then
        plainKey e0
      else
        return {
          app with subst := app.subst.map (·.abstract prefixes), familyArity := prefixes.size
        }
  else
    plainKey e0
where
  /-- Canonicalize a non-family class application. -/
  plainKey (e0 : Expr) : MetaM Key := do
    let (c, (_, subst)) ← (canonArg e0).run ({}, #[])
    let levels := match (← whnfR e0).getAppFn with
    | .const _ ls => ls
    | _ => []
    let v : Vertex := {
      name := c.getAppFn.constName?.getD .anonymous,
      pattern := c.getAppArgs,
      levels := universeLevelsOf levels
    }
    return { toVertex := v, subst }


/--
Convert an `Expr` like `Module R M` to a vertex ``{ name := `Module,
pattern := #[.bvar 0, .bvar 1], levels := polymorphic }``.
-/
public def toVertex (e : Expr) : MetaM Vertex := return (← toKey e).toVertex

/-! ## Reification -/

/--
TODO
-/
private def freshHeadAndSig? (name : Name) : MetaM (Option (Expr × Expr)) := do
  let some const := (← getEnv).find? name | return none
  let levels ← mkFreshLevelMVars const.numLevelParams
  return some (mkConst name levels, const.type.instantiateLevelParams const.levelParams levels)


/--
***Reifies*** a class `name` at the frame arguments `frame` into a valid `Expr`, wrapped as an
`Option` (if `name` is not a constant defined in the environment, or if something else went wrong,
then `none` is returned).

---
**Example**

Suppose the linter encountered the following declaration, and that `Algebra` could be weakened to
`Module` within this declaration.

```
theorem thm.{w} {S : Type 0} {A : Type w} [CommSemiring S] [Semiring A] [Algebra S A] (x : A) : … := …
```

To know what exactly it'd be suggesting (e.g., so that it can verify said suggestion candidate), the
linter needs to construct `Module S A` somehow — the weakened binder's type. To do this, it calls
`ReSynth.replBinderTypeFamilyAware` with `Algebra S A` as an `Expr` and the `Name` `` `Module ``.
This in turn then computes the frame `#[S, A]` of `Algebra S A` using `frameArgs`, and then calls
``reifyClass `Module #[S, A]``, which will output the `Expr` corresponding to `Module S A` (wrapped
as an `Option`; if `` `Module `` were not a constant defined in the environment, or if something
else went wrong, then `reifyClass` would return `none`).

Note that, in constructing its output, `reifyClass` may perform instance synthesis: in the ``
`Module `` example, it's actually constructing `@Module S A ?i₁ ?i₂`, and finds `?i₁` and `?i₂`
(instance metavariables spawned by `reifyClassGo`) via instance synthesis.
-/
public partial def reifyClass (name : Name) (frame : Array Expr) : MetaM (Option Expr) := do
  let some (head, sig) ← freshHeadAndSig? name | return none
  reifyClassGo head frame sig 0 #[] #[]
where
  /--
  Helper for `reifyClass`.

  ---
  **Example (trace)**

  Continuing the example from `reifyClass`, suppose `reifyClassGo` is tasked with reifying `Module S
  A`, with the following local context previously established by `rebuiltStatementType`'s telescope
  on `thm`'s signature:

  * `_uniq.5225` is the free variable assigned to `{S : Type 0}`. We'll write `S` instead of
    `_uniq.5225`.
  * `_uniq.5226` is the free variable assigned to `{A : Type w}`. We'll write `A` instead of
    `_uniq.5226`.
  * `_uniq.5227` is the free variable assigned to `[CommSemiring S]`. We'll write `inst₁` instead of
    `_uniq.5227`.
  * `_uniq.5228` is the free variable assigned to `[Semiring A]`. We'll write `inst₂` instead of
    `_uniq.5228`.
  * `_uniq.5229` is the free variable assigned to `[Algebra S A]` (type: `@Algebra S A inst₁
    inst₂`). We'll write `inst₃` instead of `_uniq.5229`.
  * `_uniq.5230` is the free variable assigned to `(x : A)`. This free variable is not relevant for
    us here.

  Now, before calling `reifyClassGo`, `reifyClass` will have called ``freshHeadAndSig? `Module``.
  This will have fetched the following declaration

  ```
  class Module (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] extends … where …
  ```

  ...and set ``head := `Module.{?u, ?v}`` and `sig := "(R : Type ?u) → (M : Type ?v) → [Semiring.{?u}
  R] → [AddCommMonoid.{?v} M] → Sort.{max (succ ?u) (succ ?v)}"`, where we're writing `"…"` to refer
  to the `Expr` corresponding to `…`, and `?u` and `?v` to refer to the universe level metavariables
  `?_uniq.5231` and `?_uniq.5232`.

  **Note (Instance Metavariables):** We write `?i₁` for `?_uniq.5233` and `?i₂` for `?_uniq.5234`.
  Each of these is an instance metavariable that we spawn within `reifyClassGo`, required to have
  type `Semiring.{?u} S` in the case of `?i₁` and `AddCommMonoid.{?v} A` in the case of `?i₂`.
  Instance synthesis will be used to synthesize specific values for these metavariables from the
  local context, and will assign `?i₁ := CommSemiring.toSemiring.{?u} S inst₁` and `?i₂ :=
  Semiring.toAddCommMonoid.{?v} A inst₂`.

  **Note (Auto-Generated Hygienic Instance Names):** We write `` `inst1 `` instead of
  `inst._@.Mathlib.Algebra.Module.Defs.2274493915._hygCtx._hyg.12`, the name Lean auto-generated for
  the anonymous (i.e., not named by the user) binder `[Semiring R]` of `Module`'s declaration.
  Similarly for `` `inst2 ``.

  **Warning:** `inst₁` and `` `inst1 `` are not the same.

  **Note:** In all of the calls of `reifyClassGo` below, the `head` argument is `` `Module.{?u, ?v}``,
  and the `frame` argument is `#[S, A]`.

  **1st call:** `reifyClassGo` gets called with `frameIdx = 0`, `appliedArgs = #[]`, `instMVars =
  #[]`, and the following `sig'`:

  ```
  forallE `R (Type.{?u})                                -- (no binders in scope)
    (forallE `M (Type.{?v})                             -- bvar 0 = `R
      (forallE `inst1 (Semiring.{?u} (bvar 1))          -- bvar 0 = `M, bvar 1 = `R
        (forallE `inst2 (AddCommMonoid.{?v} (bvar 1))   -- bvar 0 = `inst1, bvar 1 = `M, bvar 2 = `R
          (Sort.{max (succ ?u) (succ ?v)}))))
  ```

  **Note:** The meaning of `bvar 0` (or `bvar 1`, `bvar 2`, etc.) depends on its location within the
  expression. In general, `bvar 0` refers to the bound variable that got bound last (from the
  perspective of the location of the `bvar 0` expression within the larger expression), `bvar 1` to
  the one that got bound second last, etc.

  **2nd call:** `reifyClassGo` gets called with `frameIdx = 1`, `appliedArgs = #[S]`, `instMVars =
  #[]`, and the following `sig'`:

  ```
  forallE `M (Type.{?v})                              -- (no binders in scope)
    (forallE `inst1 (Semiring.{?u} S)                 -- bvar 0 = `M
      (forallE `inst2 (AddCommMonoid.{?v} (bvar 1))   -- bvar 0 = `inst1, bvar 1 = `M
        (Sort.{max (succ ?u) (succ ?v)})))
  ```

  **3rd call:** `reifyClassGo` gets called with `frameIdx = 2`, `appliedArgs = #[S, A]`, `instMVars
  = #[]`, and the following `sig'`:

  ```
  forallE `inst1 (Semiring.{?u} S)          -- (no binders in scope)
    (forallE `inst2 (AddCommMonoid.{?v} A)  -- bvar 0 = `inst1
      (Sort.{max (succ ?u) (succ ?v)}))
  ```

  **4th call:** `reifyClassGo` gets called with `frameIdx = 2`, `appliedArgs = #[S, A, ?i₁]`,
  `instMVars = #[?i₁]`, and the following `sig'`:

  ```
  forallE `inst2 (AddCommMonoid.{?v} A)
    (Sort.{max (succ ?u) (succ ?v)})
  ```

  **5th call:** `reifyClassGo` gets called with `frameIdx = 2`, `appliedArgs = #[S, A, ?i₁, ?i₂]`,
  `instMVars = #[?i₁, ?i₂]`, and the following `sig'`:

  ```
  Sort.{max (succ ?u) (succ ?v)}
  ```

  **Result:** Since `reifyClassGo` is tail-recursive, all the calls technically output the exact
  same result, which is also the final result: `some (Module.{0, w} S A (CommSemiring.toSemiring.{0}
  S inst₁) (Semiring.toAddCommMonoid.{w} A inst₂))`. Note that the level metavariable `?u` got
  unified with the concrete level `0`, and level metavariable `?v` got unified with the level
  _parameter_ `w` of `thm`.
  -/
  reifyClassGo (head : Expr) (frame : Array Expr) (sig' : Expr) (frameIdx : Nat)
      (appliedArgs instMVars : Array Expr) : MetaM (Option Expr) := do
    match sig' with
    -- Match outermost `.forallE` of `sig'`, thus peeling off the leftmost binder of `sig'` into
    -- `binderType` and `binderInfo`, and leaving the rest of the signature in `body`.
    | .forallE _ binderType body binderInfo =>
      if binderInfo.isInstImplicit then
        -- Instance-implicit binders get assigned metavariables for now, to be resolved by instance
        -- synthesis later on.
        let mvar ← mkFreshExprMVar binderType
        reifyClassGo head frame (body.instantiate1 mvar)
          frameIdx (appliedArgs.push mvar) (instMVars.push mvar)
      else
        -- The `frameIdx`th non-instance-implicit binder gets assigned the `frameIdx`th frame
        -- argument.
        if _ : frameIdx < frame.size then
          reifyClassGo head frame (body.instantiate1 frame[frameIdx]) (frameIdx + 1)
            (appliedArgs.push frame[frameIdx]) instMVars
        else return none
    | _ =>
      -- We've reached the end of the signature. Every frame arg must already have been consumed by
      -- now, otherwise something went wrong and we return `none`.
      unless frameIdx == frame.size do return none
      for mvar in instMVars do
        -- Synthesize an instance for each of the instance metavariables we created.
        let some inst ← (try some <$> synthInstance (← instantiateMVars (← inferType mvar))
          catch _ => pure none) | return none
        -- Assign the instance to the instance metavariable.
        mvar.mvarId!.assign inst
      -- "Instantiate" (no relation to "instance" in the sense we're using it in) the metavariables
      -- we just assigned, so that they're replaced with the instances we assigned.
      let result ← instantiateMVars (mkAppN head appliedArgs)
      -- If any `Expr` metavariables remain somehow, then something went wrong and we return `none`.
      -- (Universe level metavariables in the result are perfectly fine though.)
      if result.hasExprMVar then return none
      -- Make sure that the result is actually a class application, then return it. If it's not,
      -- return `none`.
      if (← isClass? result).isSome then return some result else return none

/--

TODO

For motivation, see `isSubsingletonClass`.


To construct `ClassGraph.isSubsingleton`, `ClassGraph.ofEnv` needs to be able to ask whether, for a
given `n`-ary class head `head`, the "generic" application `head a₁ … aₙ` is a `Subsingleton`, which
amounts to asking whether `Subsingleton (head a₁ … aₙ)` is type correct.
-/
public partial def withGenericKey {α} (name : Name) (k : Expr → MetaM (Option α)) : MetaM (Option α) := do
  let some (head, sig) ← freshHeadAndSig? name | return none
  withGenericKeyGo head sig #[] k
where
  /-- ... -/
  withGenericKeyGo {α : Type _} (head type : Expr) (applied : Array Expr)
      (k : Expr → MetaM (Option α)) : MetaM (Option α) := do
    match type with
    | .forallE binderName binderType body binderInfo =>
      if binderInfo.isInstImplicit then
        match ← (try some <$> synthInstance (← instantiateMVars binderType) catch _ => pure none) with
        | some inst => withGenericKeyGo head (body.instantiate1 inst) (applied.push inst) k
        | none =>
          withLocalDeclD binderName (← instantiateMVars binderType) fun x => do
            withNewLocalInstance ((← isClass? (← inferType x)).getD .anonymous) x do
              withGenericKeyGo head (body.instantiate1 x) (applied.push x) k
      else
        withLocalDeclD binderName binderType fun x =>
          withGenericKeyGo head (body.instantiate1 x) (applied.push x) k
    | _ =>
      let app := mkAppN head applied
      if (← isClass? app).isSome then k app else return none
