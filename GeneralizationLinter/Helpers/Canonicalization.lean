/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
module

public import Lean.Expr
public import Lean.Environment
public import Lean.Meta.Basic
public import Lean.Meta.FunInfo
public import GeneralizationLinter.Helpers.Vertex

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

/-! ## Head Helpers -/


/--
Extract the codomain (i.e., return type) of the expression, peeling off any `∀`
quantifiers in the process. This also handles dependent (and non-dependent)
arrows, since they're also implemented using `.forallE`.

Expressions that are not forall-expressions or arrow expressions are returned
as-is.

---
**Examples**

_(Examples taken from Lean docs. Their `repr`s in the notes section were
likewise taken from the Lean docs.)_

* `∀ x : Prop, x ∧ x` becomes `x ∧ x`.
* `Nat → Bool` becomes `Bool`.

---
**Notes**

* In `Expr` "notation", `∀ x : Prop, x ∧ x` is (with what `codomainOf` extracts
  "underlined"):

  ```
  Expr.forallE `x (.sort .zero) (.app (.app (.const `And []) (.bvar 0)) (.bvar 0)) .default
                                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  ```

* In `Expr` "notation", `Nat → Bool` is (with what `codomainOf` extracts
  "underlined")

  ```
  Expr.forallE `a (.const `Nat []) (.const `Bool []) .default
                                   ^^^^^^^^^^^^^^^^^
  ```
-/
public partial def codomainOf : Expr → Expr
  | .forallE _ _ b _ => codomainOf b
  | e => e

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
public def isTypeConstructor (e : Expr) : MetaM Bool := do
  match e with
  | .const c _ => return ((← getEnv).find? c).any (codomainOf ·.type |>.isSort)
  | _          => return false

/--
Given a function constant `Expr` and an array of values passed to said function,
return the array of values with all values corresponding to non-explicit binders
filtered out.

---
**Examples**

```
-- And : Prop → Prop → Prop
explicitVals And #[True, False] = #[True, False]
-- Eq : {α} → α → α → Prop
explicitVals Eq #[Nat, a, b] = #[a, b]
-- C : (α) → [Inst α] → Type
explicitVals C #[Nat, inst] = #[Nat]
```
-/
public def explicitVals (fn : Expr) (vals : Array Expr) : MetaM (Array Expr) := do
  let pinfos := (← getFunInfo fn).paramInfo
  pure <| vals.zipIdx.filterMap fun (a, i) =>
    if (pinfos[i]?.map (·.isExplicit)).getD true then some a else none

/--
Strip the universe-level arguments off of a head constant. This way,
universe-polymorphic classes canonicalize to the same vertex (e.g., `Module.{u}`
vs `Module.{v}`).

Ignoring universe levels in this way is okay in our use-case, because #TODO
-/
private def eraseHeadLevels : Expr → Expr
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
public abbrev CanonVarsM := StateT ((Std.HashMap FVarId Nat) × (Array Expr)) MetaM

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
    if ← isTypeConstructor fn then
      -- If `e` is "f a₁ … aₙ", with "f" a type constructor, then
      -- canonicalize "a₁ … aₙ" to "a₁' … aₙ'" and return "f a₁' … aₙ'".
      -- Note that "f" may be a nullary type constructor, e.g., `Nat`.
      let kept ← explicitVals fn e.getAppArgs
      return mkAppN (eraseHeadLevels fn) (← kept.mapM canonArg)
    else -- `e` is not function app, or "f" is not a type constructor
      let (m, carriers) ← get
      let k := carriers.size
      set (m, carriers.push e)
      return .bvar k -- fresh bvar

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
    .concrete ((lvls.map .normalize).toArray)
  else .polymorphic


/--
Given an `Expr` of a class application, parse it into a `ClassApp` structure.

---
**Precondition**

* `Expr` must be a class application. It should've been extracted from an
  instance implicit binder of a theorem/lemma.
-/
public def toClassApp (e: Expr) : MetaM ClassApp := do
  let e0 := e.consumeMData
  let (c, (_, carriers)) ← (canonArg e0).run ({}, #[])
  let lvls := match (← whnfR e0).getAppFn with
    | .const _ ls => ls
    | _ => []
  let v : Vertex := {
    name := c.getAppFn.constName?.getD .anonymous,
    collapsedArgs := c.getAppArgs,
    universeLevels := universeLevelsOf lvls
  }
  return { toVertex := v, carriers }


/--
Convert an `Expr` like `Module R M` to a vertex ``{ name := `Module,
collapsedArgs := #[.bvar 0, .bvar 1], universeLevels := polymorphic }``.
-/
public def toVertex (e : Expr) : MetaM Vertex := return (← toClassApp e).toVertex


/-- #TODO -/
public def Vertex.reify (v : Vertex) (carriers : Array Expr) : MetaM (Option Expr) := do
  let args := v.collapsedArgs.map (·.instantiate carriers)
  if args.any (·.hasLooseBVars) then return none
  let head ← mkConstWithFreshMVarLevels v.name
  return some (mkAppN head args)
