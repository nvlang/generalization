/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
module

public import Lean.Expr
public import Lean.Environment

/-!
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

open Lean

/--
As we walk an `Expr` (generally, a telescope), this monad helps us keep track of
two things:
* `HashMap Nat Nat`: For each `bvar n` (where `n` is some natural number
  literal) we encounter in the expression we're parsing, we add an entry `n → k`
  to this map to note to which canonical `bvar k` we've mapped `bvar n`.
* `Nat`: This keeps track of what the next de Bruijn index is that we should use
  when creating a new canonical bvar.

**Note:** We have that the next de Bruijn index is always greater than or equal
to the size of the HashMap. (Note in particular: not necessarily always equal.)
-/
public abbrev CanonM := StateM ((Std.HashMap Nat Nat) × Nat)

/--
Extract the codomain (i.e., return type) of the expression, peeling off any `∀`
quantifiers in the process. This also handles dependent (and non-dependent)
arrows, since they're also implemented using `.forallE`.

Expressions that are not forall-expressions or arrow expressions are returned
as-is.

### Examples

_(Examples taken from Lean docs. Their `repr`s in the notes section were
likewise taken from the Lean docs.)_

* `∀ x : Prop, x ∧ x` becomes `x ∧ x`.
* `Nat → Bool` becomes `Bool`.

### Notes

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
partial def codomainOf : Expr → Expr
  | .forallE _ _ b _ => codomainOf b
  | e => e

/--
#TODO
-/
partial def binderInfos (e : Expr) (bis : Array BinderInfo := #[]) : Array BinderInfo :=
  match e with
  | .forallE _ _ b bi => binderInfos b (bis.push bi)
  | _ => bis

/--
`isTypeConstructor env e` is `true` iff `e` is a (possibly nullary) type constructor
constant in `env`.

### Examples

`isTypeConstructor` returns `true` on the following:

* Nullary type constructors: `Nat`, etc.
* Unary type constructors: `Group`, `List`, etc.
* Binary type constructors: `Prod`, `And`, etc.
* etc.

`isTypeConstructor` returns `false` on the following:

* Constants that are not type constructors: `And.intro`, `Nat.succ`, etc.
* Things that are not constants: `3`, `#[3]`, `{}`, `[]`, etc.
-/
def isTypeConstructor (env : Environment) : Expr → Bool
  | .const c _ => (env.find? c).any (codomainOf ·.type |>.isSort)
  | _          => false


/--
Given a function constant `Expr` and an array of values passed to said function,
return the array of values with all values corresponding to non-explicit binders
filtered out.

### Examples

```
-- And : Prop → Prop → Prop
explicitVals env And #[True, False] -- #[True, False]
-- Eq : {α} → α → α → Prop
explicitVals env Eq #[Nat, a, b] -- #[a, b]
-- C : (α) → [Inst α] → Type
explicitVals env C #[Nat, inst] -- #[Nat]
-- Non-`.const` head
explicitVals env (.bvar 0) #[a, b] -- #[a, b]
-- Unknown constant (not in `env`)
explicitVals env UnknownConst #[a, b] -- #[a, b]
```
-/
def explicitVals (env : Environment) (fn : Expr) (vals : Array Expr) : Array Expr :=
  match fn with
  | .const c _ =>
    match env.find? c with
    | some info =>
      let bis := binderInfos info.type
      vals.zipIdx.filterMap fun (a, i) =>
        if (bis[i]?.map (·.isExplicit)).getD true then some a else none
    | none => vals
  | _ => vals

/--
Canonicalize a single binder/argument.

### Examples

* `ℕ` → `ℕ`
* `3` → `3`
* `Group G` → `Group #0`
* `Module R R` → `Module #0 #0`
* `Pow α ℕ` → `Pow #0 ℕ`
* `OfNat α 1` → `OfNat #0 1`
-/
public partial def canonArg (env : Environment) (e : Expr) : CanonM Expr := do
  let e := e.consumeMData
  match e with -- strip annotations
  | .bvar n => -- bvars get their index canonicalized
    let (m, next) ← get -- get state from CanonM
    match m[n]? with
    | some k => return .bvar k -- we've seen this bvar before
    | none   => -- new bvar
      set (m.insert n next, next + 1) -- update CanonM state
      return .bvar next
  | .lit (.natVal _) => return e -- nat literals are kept as-is
  | _ =>
    let fn := e.getAppFn
    if isTypeConstructor env fn then
      -- If `e` is "f a₁ … aₙ", with "f" a type constructor, then
      -- canonicalize "a₁ … aₙ" to "a₁' … aₙ'" and return "f a₁' … aₙ'".
      -- Note that "f" may be a nullary type constructor, e.g., `Nat`.
      return mkAppN fn (← (explicitVals env fn e.getAppArgs).mapM (canonArg env))
    else -- `e` is not function app, or "f" is not a type constructor
      let (m, next) ← get
      set (m, next + 1)
      return .bvar next -- fresh bvar
