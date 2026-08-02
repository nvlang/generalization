/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
module

public import Lean.Meta.Basic
public import GeneralizationLinter.Graph.Vertex
import Lean.Meta.AppBuilder
import Lean.Meta.AbstractMVars

open Lean Meta

namespace GeneralizationLinter

/-!
# Canonicalization

This module is responsible for converting class applications of any kind into `Vertex`s or `Key`s,
which is the process we refer to as ***canonicalization***, and back, which we refer to as
***reification***.

**Main definitions:**

* `keySlots` tries to figure out what parameter "slots" of a class are recoverable from the others,
  which are slots that we don't want to index our class graph with. For instance, for `Module R M
  inst₁ inst₂`, the key slots are the first two parameter slots (corresponding to `R` and `M`).
* `canonArg` canonicalizes a single argument. For example, for `Module R M`, this means `R` and `M`
  become `#0` and `#1`. For `Pow α ℕ`, this means `α` becomes `#0` and `ℕ` remains `ℕ`.
* `canonKey` canonicalizes a class application into a `Key` that we query the class graph with.
* `mkClassApp?` takes a class name and its key arguments, and reifies them into a proper class
  application.
* `reifyKey?` takes a class name and a `pattern` and corresponding `subst`, and reifies them into a
  proper class application.
-/

open Lean Meta GeneralizationLinter
open Std (HashMap)

/-! ## Head Helpers -/

/--
`isTypeFormerConst e` is `true` iff `e` is a (possibly nullary) type former
constant, i.e., a constant whose type ends in a `Sort`.

---
**Examples**

`isTypeFormerConst` returns `true` on the following:

* Nullary type formers: `Nat`, etc.
* Unary type formers: `Group`, `List`, etc.
* Binary type formers: `Prod`, `And`, etc.
* etc.

`isTypeFormerConst` returns `false` on the following:

* Constants that are not type formers: `And.intro`, `Nat.succ`, etc.
* Things that are not constants: `3`, `#[3]`, `{}`, `[]`, etc.
-/
public def isTypeFormerConst (env : Environment) (e : Expr) : Bool :=
  match e with
  | .const c _ => (env.find? c).any (·.type.getForallBody.isSort)
  | _          => false

initialize synonymFormerCacheRef : IO.Ref (Std.HashMap Name Bool) ← IO.mkRef {}

/--
Is `h` a "synonym type former", i.e., a former that unfolds to one of its own arguments.

---
**Examples**

```
isSynonymFormer `Monoid = false
isSynonymFormer `OrderDual = true
```
-/
public def isSynonymFormer (h : Name) : MetaM Bool := do
  if let some r := (← synonymFormerCacheRef.get)[h]? then return r
  let some info := (← getEnv).find? h | return false
  let r ← try
      let .defnInfo di := info | pure false
      forallTelescope di.type fun args _ => do
        let app := mkAppN (mkConst h (di.levelParams.map (Level.param ·))) args
        let red ← withTransparency .all (whnf app)
        pure (args.any (red == ·))
    catch _ => pure false
  synonymFormerCacheRef.modify (·.insert h r)
  return r

/-! ## What to keep -/

initialize keySlotsCacheRef : IO.Ref (HashMap Name (Array Bool)) ← IO.mkRef {}

/--
Is `const`'s `i`th slot recoverable from the values of the slots `kept` still marks as kept?

We answer by running the recovery rather than predicting it: unify each kept binder's type, taken in
normal form, against a fully-metavariable copy of `const`'s telescope, and report whether slot `i`'s
metavariable came out assigned. Normal form is what makes this a test rather than a tautology — an
argument reaching a call site carries whatever type it happens to have, not the one `const` declares
— so a former that unfolds away its argument leaves the metavariable unassigned, while one that
cannot unfold still pins it.

Restricting to `kept` is what makes the mask self-supporting: a slot must be recoverable from what
actually survives, not from another slot that is itself about to be dropped.

---
**Examples**

Writing `recoverableFrom C i` for the call on `C`'s own telescope with every non-instance slot kept:

```
-- structure Subtype {α : Sort u} (p : α → Prop)
recoverableFrom `Subtype 0 = true     -- `p`'s type `α → Prop` pins `α`
recoverableFrom `Subtype 1 = false    -- no other binder's type mentions `p`
-- class IsPreorder (α : Sort*) (r : α → α → Prop)
recoverableFrom `IsPreorder 0 = true  -- same shape: the relation pins the carrier
-- class Module (R M : Type*) [Semiring R] [AddCommMonoid M]
recoverableFrom `Module 0 = false     -- only `[Semiring R]` mentions `R`, and `kept` excludes it
```
-/
private def recoverableFrom (const : ConstantInfo) (binders : Array LocalDecl)
    (kept : Array Bool) (i : Nat) : MetaM Bool :=
  -- the unification below assigns metavariables; keep those assignments off the ambient context
  withNewMCtxDepth do
  let (mvars, _, _) ← forallMetaTelescope const.type
  let some mvᵢ := mvars[i]? | return false
  for j in [0:binders.size] do
    -- only slots that survive may be used to recover slot `i`; a slot that is itself about to be
    -- dropped cannot be what makes another one droppable
    if j == i || !kept[j]! then continue
    let some mv := mvars[j]? | return false
    -- Note that `isDefEq` assigns mvars via unification.
    unless ← isDefEq (← inferType mv) (← whnf binders[j]!.type.cleanupAnnotations) do return false
  return !(← instantiateMVars mvᵢ).isMVar -- did the unification solve slot `i`?


/--
Given a head constant `head`, return a boolean mask `#[b₁ … bₙ]` (`bᵢ : Bool`) such that `bᵢ` is
`true` iff the `i`th slot of `head` is one that should be kept when converting an application of
`head` into a `Key` or into an entry of a different `Key`'s `pattern`. Note that `keySlots` is used
not only for classes, but for all kinds of type formers.

Instance implicit slots are always dropped, while other slots are dropped only if their values are
recoverable from the values of the kept slots.

The two drops rest on different grounds: a non-instance slot is dropped because unification recovers
it (see `recoverableFrom`), an instance slot because `mkClassApp?` re-synthesizes it — which can
fail, and which agrees with the original only under instance coherence. Instance slots are also kept
out of `recoverableFrom`'s pool: their types mention the carriers, so admitting them would make each
carrier look recoverable — pinned by its own instance argument — and drop it out of the key.

---
**Examples**

```
-- class Module (R M : Type*) [Semiring R] [AddCommMonoid M]
keySlots `Module = #[true, true, false, false]
-- class Small (α : Type*)
keySlots `Small = #[true]
-- structure Subtype {α : Sort u} (p : α → Prop)
keySlots `Subtype = #[false, true]
-- class IsWellFounded (α : Type*) (r : α → α → Prop)
keySlots `IsWellFounded = #[false, true]
-- structure Submodule (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]
keySlots `Submodule = #[true, true, false, false, false]
```
-/
def keySlots (head : Name) : MetaM (Array Bool) := do
  if let some m := (← keySlotsCacheRef.get)[head]? then return m -- cache hit
  let some info := (← getEnv).find? head | return #[]
  let slots ← forallTelescope info.type fun params _ => do
    let decls ← params.mapM (·.fvarId!.getDecl)
    -- Instance implicit params are always dropped; the rest start kept and are dropped in turn.
    -- The order decides only which of two mutually recoverable slots survives, since dropping one
    -- takes it out of the pool the remaining tests draw on. Testing the least visible binders first
    -- lets an explicit slot win such a tie: those are the arguments a reader writes at a use site,
    -- so they are the ones worth keeping in the key.
    let visibility (i : Nat) : Nat := match decls[i]!.binderInfo with
      | .strictImplicit => 0 | .implicit => 1 | _ => 2
    let order := (Array.range params.size).qsort fun a b =>
      if visibility a == visibility b then a < b else visibility a < visibility b
    let mut keep := decls.map (!·.binderInfo.isInstImplicit)
    for i in order do
      unless keep[i]! do continue
      if ← try recoverableFrom info decls keep i catch _ => pure false then
        keep := keep.set! i false
    return keep
  keySlotsCacheRef.modify (·.insert head slots) -- cache result
  return slots


/--
The ***key arguments*** of an application `fn a₁ … aₙ` (`vals = #[a₁, …, aₙ]`), in accordance with
`keySlots` applied to `fn`'s head constant. If `fn` isn't a constant, all of `vals` is kept.

---
**Examples**

```
-- class Module (R M : Type*) [Semiring R] [AddCommMonoid M]
keyArgs ‹Module› #[R, M, inst₁, inst₂] = #[R, M]
-- structure Subtype {α : Sort u} (p : α → Prop)
keyArgs ‹Subtype› #[α, p] = #[p]
-- `f` a free variable
keyArgs ‹f› #[a, b] = #[a, b]
```
-/
public def keyArgs (fn : Expr) (vals : Array Expr) : MetaM (Array Expr) := do
  let slots ← match fn.constName? with
    | some head => keySlots head
    | none => pure #[] -- non-const head ⟹ keep all vals
  pure <| vals.zipIdx.filterMap fun (val, i) =>
    if slots[i]?.getD true then some val else none -- keep by default


/--
Given `mask = #[b₁, …, bₙ]` and `vals = #[e₁, …, eₘ]`:
* If the number of `true` entries in `mask` is not `m`, returns `none`.
* Otherwise, returns `#[s₁, …, sₙ]`, where `sᵢ = some eₖ` if `bᵢ` is the `k`th `true` entry of
  `mask`, and `sᵢ = none` if `bᵢ == false`.

---
**Example**

```
placeAtSlots? #[false, true] #[e₁] = some #[none, some e₁]
```
-/
def placeAtSlots? (mask : Array Bool) (vals : Array Expr) : Option (Array (Option Expr)) := Id.run do
  let mut slots : Array (Option Expr) := #[]
  let mut i : Nat := 0
  for b in mask do
    if b then
      let some v := vals[i]? | return none
      slots := slots.push (some v)
      i := i + 1
    else
      slots := slots.push none
  if i == vals.size then return some slots else return none


/--
Used to strip the universe-level arguments off the heads of type formers used within a key slot. We
delegate all handling of universe levels to `Vertex.levels`.
-/
public def eraseConstLevels : Expr → Expr
  | .const c _ => .const c []
  | e => e


/--
Retrieves the value of a `Nat`-valued argument.

---
**Examples**

* `.lit (.natVal n)` → `some n`
* `@OfNat.ofNat ℕ n _` → `some n`
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

* `HashMap FVarId Nat`: For each `fvar id` (where `id` is some `FVarId`) that we
  canonicalize as a whole argument, we add an entry `id → k` to this map to note
  to which canonical `bvar k` we've mapped `fvar id`.
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
* `Group G` → `Group #0`
* `Module R R` → `Module #0 #0`
* `Pow α ℕ` → `Pow #0 ℕ`
* `OfNat α 1` → `OfNat #0 1`
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
    if isTypeFormerConst (← getEnv) fn then
      -- If `e` is "f a₁ … aₙ", with "f" a type constructor, then canonicalize the key arguments
      -- among "a₁ … aₙ" (see `keyArgs`) to "b₁ … bₖ" and return "f b₁ … bₖ", with "f" stripped of
      -- its universe levels. Note that "f" may be a nullary type former, e.g., `Nat`.
      let kept ← keyArgs fn e.getAppArgs
      return mkAppN (eraseConstLevels fn) (← kept.mapM canonArg)
    -- If `e` has no "variables", i.e., it is essentially a constant or tower of constants, then we
    -- just leave it as is.
    else if !e.hasFVar && !e.hasMVar && !e.hasLevelParam then
      return e
    else
      -- `e` contains "variables", is not merely an fvar, and is either not a function app, or is
      -- one whose "f" is not a type constructor. In this case, we abstract `e` to a fresh bvar,
      -- and record `e` so that `reifyKey?` can recover it later on.
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
universeLevelsOf [0, 1] = .concrete #[0, 1]
universeLevelsOf [u]    = .polymorphic     -- `u` is a universe variable
universeLevelsOf []     = .concrete #[]    -- monomorphic class, e.g., `Fact`
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
  := #[.bvar 0, .bvar 0]`.
* For a parametric class binder like `∀ prefix, C args`, the body (`C args`) determines the `Vertex`
  fields, while the parametric index in the prefix is abstracted to a bvar. So, for example, for `[∀
  i : ι, Monoid (f i)]`, where `f : ι → Type*` is some free variable, we'd have ``name := `Monoid``,
  `pattern := #[.bvar 0]`, `subst := #[f (.bvar 0)]`, and `forallArity := 1`.
* If the body of such a Π-binder doesn't canonicalize to a constant-headed application (so the head
  name would come out `.anonymous`), we instead canonicalize the whole Π-expression as one opaque
  carrier. For `∀ n : ℕ, P n`, with `P` a free variable, this yields `name := .anonymous`, `pattern
  := #[]`, `subst := #[∀ n : ℕ, P n]`, and `forallArity := 0`.

---
**Examples**

```
-- class Module (R M : Type*) [Semiring R] [AddCommMonoid M]
canonKey ‹@Module R M inst₁ inst₂› = {
  -- `Vertex` fields
  name := `Module,
  levels := .polymorphic
  pattern := #[.bvar 0, .bvar 1],
  -- `Key` fields
  subst := #[R, M],
  forallArity := 0,
}

-- class Small (α : Type*)
-- structure Subtype {α : Sort u} (p : α → Prop)
canonKey ‹@Small (@Subtype α p)› = {
  -- `Vertex` fields
  name := `Small,
  levels := .polymorphic
  pattern := #[Subtype (.bvar 0)],
  -- `Key` fields
  subst := #[p],
  forallArity := 0,
}

-- Let `f` be a free variable with `f : ι → Type*`.
canonKey ‹∀ i : ι, Monoid (f i)› = {
  -- `Vertex` fields
  name := `Monoid,
  levels := .polymorphic
  pattern := #[.bvar 0],
  -- `Key` fields
  subst := #[f (.bvar 0)]
  forallArity := 1,
}
```

Note how the class application `Small (Subtype p)` gets indexed in the class graph in accordance
with what `keySlots` returns for the type former `Subtype`, which is not itself a class.
-/
public def canonKey (e : Expr) : MetaM Key := do
  let e0 := e.consumeMData
  if (← whnfR e0).isForall then
    forallTelescopeReducing e0 fun prefixes body => do
      let app ← plainKey (body.consumeMData)
      if app.name == .anonymous then
        plainKey e0
      else
        return {
          app with subst := app.subst.map (·.abstract prefixes), forallArity := prefixes.size
        }
  else
    plainKey e0
where
  /-- Canonicalize a class application without decomposing any Π-prefix. -/
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


/-! ## Reification -/

/--
Returns pair consisting of:

1.  A constant named `name` at fresh level metavariables, and
2.  the constant's type, instantiated at those metavariables.

Returns `none` if `name` isn't in the environment.

---
**Implementation notes**

The fresh universe level metavariables are what enable us to reify a universe-polymorphic class
without having to pin its levels prematurely. Note that reification is handed only a class name, a
`pattern` and a `subst` — never a `Vertex.levels` tag — so we have to add levels to `name` in some
way anyhow, and we're just choosing not to give it arbitrarily pinned levels, but rather
giving it fresh level metavariables and letting downstream unification pin them if and where
necessary.
-/
def freshHeadAndSig? (name : Name) : MetaM (Option (Expr × Expr)) := do
  let some const := (← getEnv).find? name | return none
  let levels ← mkFreshLevelMVars const.numLevelParams
  return some (mkConst name levels, const.type.instantiateLevelParams const.levelParams levels)


/--
Is this instance goal ready to be synthesized? Its non-`outParam` arguments must hold no unassigned
metavariables (since `outParam` arguments are precisely the ones synthesis is expected to
determine).

`whnfR` matters here: `FunLike` is a `def` over `DFunLike`, and only the latter is registered with
the out-parameter positions `#[1, 2]`.
-/
private def instanceGoalReady (ty : Expr) : MetaM Bool := do
  let ty ← whnfR (← instantiateMVars ty)
  let some cls := ty.getAppFn.constName? | return !ty.hasExprMVar
  let outs := ((classExtension.getState (← getEnv)).outParamMap.find? cls).getD #[]
  return ty.getAppArgs.zipIdx.all fun (arg, i) => outs.contains i || !arg.hasExprMVar


/--
***Reifies*** a class `name` at its key arguments `vals` (see `keySlots`) into a valid `Expr`,
wrapped as an `Option` (if `name` is not a constant defined in the environment, or if something else
went wrong, then `none` is returned).

---
**Example**

Suppose the linter encountered the following declaration, and that `Algebra` could be weakened to
`Module` within this declaration.

```
theorem thm.{w} {S : Type 0} {A : Type w} [CommSemiring S] [Semiring A] [Algebra S A] (x : A) : … := …
```

To know what exactly it'd be suggesting (e.g., so that it can verify said suggestion candidate), the
linter needs to construct `Module S A` somehow — the weakened binder's type. To do this, it calls
`replaceBinderType?` with `Algebra S A` as an `Expr` and the replacement `Vertex` for `Module S A`.
This in turn then computes the key of `Algebra S A` (which has `subst = #[S, A]`), and then calls
``reifyKey? `Module #[.bvar 0, .bvar 1] #[S, A]``, which then calls ``mkClassApp? `Module #[S, A]``,
which will in turn output the `Expr` corresponding to `Module S A` (wrapped
as an `Option`; if `` `Module `` were not a constant defined in the environment, or if something
else went wrong, then `mkClassApp?` would return `none`).

Note that, in constructing its output, `mkClassApp?` may perform instance synthesis: in the ``
`Module `` example, it's actually constructing `@Module S A ?i₁ ?i₂`, and finds `?i₁` and `?i₂`
(instance metavariables spawned by `mkClassApp?`) via instance synthesis.
-/
public def mkClassApp? (name : Name) (vals : Array Expr) : MetaM (Option Expr) := do
  -- as `mkAppOptM` does: the unification and synthesis below must not assign metavariables of the
  -- ambient context, or they leak into whatever the caller does next
  let some abst ← withNewMCtxDepth build | return none
  -- `withNewMCtxDepth` restores the whole metavariable context on exit, so `build` hands back its
  -- leftover universes as parameters; reopening turns them into metavariables the caller owns.
  return some (← openAbstractMVarsResult abst).2.2
where
  /-- The application itself, built one metavariable depth down. -/
  build : MetaM (Option AbstractMVarsResult) := do
  let mask ← keySlots name
  let some slots := placeAtSlots? mask vals | return none
  let some (head, sig) ← freshHeadAndSig? name | return none
  let (margs, binderInfos, _) ← forallMetaTelescope sig
  unless margs.size == slots.size do return none
  for i in [0:margs.size] do
    if let some v := slots[i]! then
      unless ← isDefEq margs[i]! v do return none
  -- Instance goals are synthesized to a fixpoint rather than in binder order: a goal whose
  -- non-`outParam` arguments are still unknown can become solvable once another goal is solved.
  -- `mkAppOptM` synthesizes in order (`Lean/Meta/AppBuilder.lean`, `mkAppMFinal`), and so fails on
  -- `IsLocalHom f`, where `[Monoid ?R]` precedes the `[FunLike ?F ?R ?S]` that determines `?R`.
  let mut pending := (Array.range margs.size).filter fun i => binderInfos[i]!.isInstImplicit
  for _ in [0:margs.size + 1] do
    if pending.isEmpty then break
    let mut still : Array Nat := #[]
    for i in pending do
      if ← margs[i]!.mvarId!.isAssigned then continue
      let ty ← instantiateMVars (← inferType margs[i]!)
      if ← instanceGoalReady ty then
        let some inst ← (try some <$> synthInstance ty catch _ => pure none) | return none
        margs[i]!.mvarId!.assign inst
      else still := still.push i
    if still.size == pending.size then break -- a whole pass without progress
    pending := still
  let result ← instantiateMVars (mkAppN head margs)
  -- `hasExprMVar` is syntactic, so it rejects ambient metavariables too, not just our own.
  if result.hasExprMVar then return none
  unless (← isClass? result).isSome do return none
  -- A universe the key arguments do not pin stays open: in `Small.{u, v} (α : Type v)` the argument
  -- fixes `v`, not `u`. The caller pins it later, but it must not outlive this depth, so abstract
  -- it. `abstractMVars` parametrizes the universes minted here and leaves ambient ones alone.
  return some (← abstractMVars result)


/--
Essentially the inverse of `canonArg`.

Here, `e` is a `pattern` entry of a class graph vertex `v : Vertex` and `reifyArg? e subst` is tasked
with reifying this `e` using the `subst` field of some key `k : Key` for which `k.toVertex = v`. In
the vast majority of cases, `e` is just a plain bvar and `reifyArg?` just returns the corresponding
`subst` entry. However, if `e` is a constant-headed, non-nullary application, it'll return `e`
_re-elaborated_ (i.e., with the non-key args which `canonArg` dropped inferred back, and fresh
universe levels applied and determined, since `canonArg` erases universe levels too) with any bvars
in any of its arguments replaced using `subst`.

---
**Examples**

```
reifyArg? ‹#0› #[α] = some ‹α›
reifyArg? ‹#0› #[Fintype.card α] = some ‹Fintype.card α›
reifyArg? ‹Int› #[] = some ‹Int›
reifyArg? ‹42› #[] = some ‹42›
reifyArg? ‹Units #0› #[α] = some ‹Units α›
reifyArg? ‹Subtype #0› #[p] = some ‹@Subtype α p›
```
-/
public partial def reifyArg? (e : Expr) (subst : Array Expr) : MetaM (Option Expr) := do
  match e with
  -- If `e` is a bvar, `subst` tells us exactly what it should be "elaborated" into (`subst`'s
  -- entries are already fully elaborated, after all, since they're just subexpressions of the
  -- elaborated expression that gave rise to the key which contains `subst`).
  | .bvar i => return subst[i]?
  | _ =>
    -- If `e` is not a constant-headed application (e.g., `e = .sort 0` or `e = .lit (.natVal 42)`),
    -- we return `some e`, because `canonArg` would've left `e` untouched anyway. This happens very
    -- rarely though (<1% of cases).
    let some h := e.getAppFn.constName? | return some e
    let args := e.getAppArgs
    -- At this point, `e` is `h arg₁ … argₙ`, `h` is a constant, `args = #[arg₁, …, argₙ]`. If `h`
    -- is nullary, we return `e` as is. Example: `e = ℝ = .const Real []` (so that ``h = `Real``).
    if args.isEmpty then return some e
    let keep ← keySlots h
    -- The `args.isEmpty` check above already rules out the case where `keySlots h` is `#[]` because
    -- `h` is nullary; what it doesn't rule out is `h` not being in the environment, but this can't
    -- really happen for a pattern entry, since its constants come from an `Expr` elaborated in this
    -- same environment.
    if keep.isEmpty then return some e
    let mut vals : Array Expr := #[]
    for arg in args do
      -- `return none` branch taken via one of the two `return none`s further below.
      let some arg' ← reifyArg? arg subst | return none
      vals := vals.push arg'
    -- `return none` branch taken very rarely (<1% of cases), corresponding to cases where
    -- `canonArg` canonicalized a type former that was only _partially_ applied, so that `vals.size
    -- < keep.size`. Example: `reifyArg? ‹Except #0› #[ℕ] = none`.
    let some slots := placeAtSlots? keep vals | return none
    -- Let `mkAppOptM` do the heavy lifting. `return none` branch taken very rarely (<1% of cases),
    -- corresponding to cases of type former applications where the former's universe params aren't
    -- fully determined by the args in `slots`, leading to `mkAppOptM` throwing (it returns an
    -- `Expr`, not an `Option Expr`, and signals failure by throwing).
    -- Example: `reifyArg? ‹ULift #0› #[ℕ] = none`.
    try some <$> mkAppOptM h slots catch _ => return none


/--
Essentially the inverse of `canonKey` for non-parametric class binders. Reifies the class `name` by
instantiating the `pattern` of its key with the concrete values provided by `subst`, each elaborated
against the corresponding slot's expected type, and then inferring the non-key-slots of `name`.
Returns `none` if `pattern` needs more values than `subst` provides, or if elaboration or inference
failed at any point.

---
**Example**

```
-- class Module (R M : Type*) [Semiring R] [AddCommMonoid M]
-- In a context with `S A : Type` and instances `[CommSemiring S] [Semiring A]`:
reifyKey? `Module #[.bvar 0, .bvar 1] #[S, A] = some ‹@Module S A inst₁ inst₂›
-- (`inst₁` and `inst₂` are synthesized by `mkClassApp?`.)
```
-/
public def reifyKey? (name : Name) (pattern subst : Array Expr) : MetaM (Option Expr) := do
  if pattern.any (·.looseBVarRange > subst.size) then return none
  let mut entries : Array Expr := #[]
  for p in pattern do
    -- Pattern entries can be applications, in which case `subst` won't tell us what the pattern
    -- entry is, but rather what its key arguments are. So we delegate figuring either case out to
    -- `reifyArg?`.
    let some e ← reifyArg? p subst | return none
    entries := entries.push e
  mkClassApp? name entries


/--
Run the continuation `k` on the "generic" application `name.{…} a₁ … aₙ` of `n`-ary class `name` on
fresh local hypotheses `a₁`, …, `aₙ` plus the WHNF-reduced body of `name`'s signature (which
corresponds to the signature's conclusion only if said conclusion has no leading `∀`-expressions
that `forallTelescopeReducing` would peel off).

Returns `none` without ever running `k` if `name` isn't in the environment, or if the generic
application isn't a class application.

For motivation, see `isSubsingletonClass`.

---
**Examples**

```
withGenericClassApp `Small k = k ‹@Small.{?w, ?v} α› ‹Prop›
withGenericClassApp `Module k = k ‹@Module.{?u, ?v} R M inst₁ inst₂› ‹Type (max ?u ?v)›
withGenericClassApp `Nat.succ k = none
```
-/
public def withGenericClassApp {α} (name : Name) (k : Expr → Expr → MetaM (Option α)) :
    MetaM (Option α) :=
  -- the fresh level metavariables minted below, and whatever `k` assigns while inspecting the
  -- generic application, must not escape into the ambient context
  withNewMCtxDepth do
  -- `head` is `name` with universe levels, i.e., `name.{…}`.
  let some (head, sig) ← freshHeadAndSig? name | return none
  forallTelescopeReducing (whnfType := true) sig fun params body => do
    let app := mkAppN head params
    if (← isClass? app).isSome then k app body else return none
