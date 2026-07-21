/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
module

public import Lean.Expr
import Batteries.Data.List.Basic

namespace GeneralizationLinter

/-!
TODO: Module docstring.
-/

open Lean
open Std (HashMap)

/-- Describes universe polymorphism (or lack thereof) for vertices. -/
public inductive UniverseLevels
  | polymorphic -- universe-polymorphic
  | concrete (levels : Array Level) -- specific universe levels only
  deriving BEq, Hashable, Inhabited

/--
A vertex of the class graph.
-/
public structure Vertex where
  /--
  Name of the typeclass.

  Example:
  * `Module R M` → `Module`
  -/
  name : Name

  /--
  Key arguments (see `keyArgs`), with constants passed through and everything else canonicalized to
  bvars (though structured arguments keep their structure). For the bvars, the only information that
  is preserved is which, if any, of the arguments were equal to one another.

  ---
  **Examples**

  | Class application | `pattern` | Notes |
  |:----|:----|:----|
  | `Module R M` | `#[bvar 0, bvar 1]` | fvars become bvars |
  | `SomeClass α β γ β` | `#[bvar 0, bvar 1, bvar 2, bvar 1]` | repeated fvars reuse bvar index |
  | `Pow α ℕ` | `#[bvar 0, ℕ]` | bare constant is preserved |
  | `IsTrans α (·=·)` | `#[bvar 0, bvar 1]` | opaque relation becomes bvar |
  | `OfNat α 1` | `#[bvar 0, 1]` | nat literal is preserved |
  | `Monoid (List α)` | `#[List (bvar 0)]` | structure inside carrier is preserved |
  | `Monoid (List (List (α × β)))` | `#[List (List ((bvar 0) × (bvar 1)))]` | structure inside carrier is preserved |
  | `Module (α × β) M` | `#[(bvar 0) × (bvar 1), bvar 2]` | structure inside carrier is preserved |
  -/
  pattern : Array Expr

  /--
  If the typeclass is universe polymorphic, this is indicated through a single value `.polymorphic`.
  If the typeclass's universe levels are concrete, they are all specified through `.concrete #[u₁ …
  uₙ]`, where e.g. `u₁` might be 0 (i.e., not a variable). The fact that we treat all universe
  polymorphism the same can lead to problems.

  For example, consider the following instance:

  ```
  instance CategoryTheory.locallySmall_self.{v, u} (C : Type.{u})
    [inst : CategoryTheory.Category.{v, u} C] : CategoryTheory.LocallySmall.{v, v, u} C inst
  ```

  When scanning this instance, `extractEdge?` will mint the following edge:

  ```
  {
    src := { name := ``CategoryTheory.Category, pattern := #[#0], levels := .polymorphic },
    tgt := { name := ``CategoryTheory.LocallySmall, pattern := #[#0], levels := .polymorphic }
  }
  ```

  The fact that the real target was `LocallySmall.{v, v, u}` and not `LocallySmall.{w, v, u}` is
  lost. This could lead to unsound candidates that the verifier must catch. However, most of the
  time, the target levels are pinned indirectly by `Vertex.pattern`. For example:

  ```
  instance ContinuousAdd.to_continuousVAdd.{u} {M : Type.{u}}
    [inst₁ : TopologicalSpace.{u} M]
    [inst₂ : Add.{u} M]
    [inst₃ : ContinuousAdd.{u} M inst₁ inst₂] :
    ContinuousVAdd.{u, u} M M (instVAddOfAdd.{u} M inst₂) inst₁ inst₁
  ```

  When scanning this instance, `extractEdge?` will mint the following edge:

  ```
  {
    src := { name := ``ContinuousAdd, pattern := #[#0], levels := .polymorphic },
    tgt := { name := ``ContinuousVAdd, pattern := #[#0, #0], levels := .polymorphic }
  }
  ```

  Here, even though the information about the universe levels appears lost, it is actually pinned by
  `pattern := #[#0, #0]`, because the two arguments that the pattern refers to are tied to the two
  universe levels:

  ```
  class ContinuousVAdd.{u, v}
    (M : Type.{u}) (X : Type.{v}) -- Note: M = X ⟹ u = v
    [inst₁ : VAdd.{u, v} M X]
    [inst₂ : TopologicalSpace.{u} M]
    [inst₃ : TopologicalSpace.{v} X] :
    Prop
  ```

  Future work could include making the handling of universe levels more precise, though we
  hypothesize the gains from this may be modest.
  -/
  levels : UniverseLevels
  deriving BEq, Hashable, Inhabited

/--
A specific class application parsed at runtime into a (canonicalized) vertex together with the
original values of the canonicalized arguments.
-/
public structure Key extends Vertex where
  /--
  The concrete terms abstracted by `pattern`'s bvars: `subst[k]` is the term that `bvar k` stands
  for.

  ---
  **Examples**

  | Class application | `pattern` | `subst` |
  |:----|:----|:----|
  | `Module R M` | `#[bvar 0, bvar 1]` | `#[R, M]` |
  | `SomeClass α β γ β` | `#[bvar 0, bvar 1, bvar 2, bvar 1]` | `#[α, β, γ]` |
  | `Pow α ℕ` | `#[bvar 0, ℕ]` | `#[α]` |
  | `IsTrans α (·=·)` | `#[bvar 0, bvar 1]` | `#[α, (·=·)]` |
  | `OfNat α 1` | `#[bvar 0, 1]` | `#[α]` |
  | `Monoid (List α)` | `#[List (bvar 0)]` | `#[α]` |
  | `Monoid (List (List (α × β)))` | `#[List (List ((bvar 0) × (bvar 1)))]` | `#[α, β]` |
  | `Module (α × β) M` | `#[(bvar 0) × (bvar 1), bvar 2]` | `#[α, β, M]` |

  ---
  **Implementation notes**

  This property is currently unused. It's written to by `reifyVert`, but never read. This is because
  the functions that would need it have access to the original class applications whose concrete
  terms this field contains, so these functions just use that instead, since it's somewhat simpler.
  However, `subst` could become useful in the future, if we ever try to transport arguments across
  weakening edges (so that a weakening like `[Class A B] ↝ [Class' B A]` can be distinguished from a
  weakening like `[Class A B] ↝ [Class' A B]`).
  -/
  subst : Array Expr

  /--
  Length of the decomposed Π-prefix of a family application, 0 (default) for an ordinary
  application. The prefix itself isn't stored, but rederived from the original binder type later on.

  ---
  **Examples**

  ```
  [Group G]             -- familyArity := 0
  [∀ i, C (f i)]        -- familyArity := 1
  [∀ i [D i], C (f i)]  -- familyArity := 2
  ```
  -/
  familyArity : Nat := 0
  deriving Inhabited

/--
First-order¹ syntactic matcher.

¹ First-order means that no bvar in the pattern may represent the head of a ≥1-arity application.
  For example, matching `List Nat` against `List #0` is fine, but matching it against `#0 Nat` is
  not.

---
**Example**

-/
private partial def matchE (env : HashMap Nat Expr) (pattern target : Expr) :
    Option (HashMap Nat Expr) :=
  match pattern with
  -- `j` is the bvar's de Bruijn index. The first occurrence of a bvar in a pattern will match any
  -- `target`, but once a bvar from the pattern is matched, it is bound to the target it matched,
  -- and all subsequent occurrences of that bvar in the pattern will have to match the same value.
  | .bvar j => match env[j]? with
    -- `.bvar j` was already bound to `e : Expr`.
    | some e => if e == target then some env else none
    -- First occurrence of `.bvar j` in `pattern`
    | none => some (env.insert j target)
  | _ =>
    -- If the pattern is an application, then check that the target is also an application of the
    -- same head and arity. If it is, recurse into the applications' arguments. For example, a
    -- pattern `fn (.bvar 0) (.bvar 1) (.bvar 0)` would match `fn 3 4 3`, but not `fn' 3 4 3` or `fn
    -- 3 4 4`.
    if pattern.isApp then
      if target.isApp &&
          pattern.getAppFn == target.getAppFn &&
          pattern.getAppArgs.size == target.getAppArgs.size then
        (pattern.getAppArgs.zip target.getAppArgs).foldlM (fun env (p, t) => matchE env p t) env
      else none
    else if pattern == target then some env else none

/--
Returns `true` iff `pattern` subsumes `target`.

---
**Examples**

```
subsumes #[.bvar 0] #[4]                -- true
subsumes #[.bvar 0] #[4, 2]             -- false: size mismatch
subsumes #[.bvar 0, .bvar 1] #[4]       -- false: size mismatch
subsumes #[.bvar 0, .bvar 1] #[4, 2]    -- true
subsumes #[.bvar 0, .bvar 1] #[4, 4]    -- true
subsumes #[.bvar 0, .bvar 0] #[4, 2]    -- false: 2nd occurrence of `.bvar 0` doesn't match 1st
subsumes #[.bvar 0, .bvar 0] #[4, 4]    -- true
subsumes #[.bvar 0] #[List Nat]         -- true
subsumes #[List (.bvar 0)] #[List Nat]  -- true
```
-/
public def subsumes (pattern target : Array Expr) : Bool :=
  pattern.size == target.size &&
    ((pattern.zip target).foldlM (fun env (p, t) => matchE env p t) ({} : HashMap Nat Expr)).isSome

/--
Given

* an array `bvarColors` such that `bvarColors[i]` is the color of `.bvar i`, and
* an expression `color`,

return a list of 2-tuples representing, in the first coordinate, each possible de Bruijn index
(i.e., bvar) we may assign to `color`, and in the second coordinate, the `bvarColors` array that
would result from that assignment.

---
**Example**

Suppose we want to see all the ways in which the arguments of `f ℕ ℕ ℤ ℕ` can be abstracted
(counting only abstractions under which _every_ argument gets abstracted). This is equivalent to
solving the following combinatorial problem:

> Given the following numbered, colored balls, how many ways are there to partition the balls into
> monochromatic groups?
>
> * Ball 1, colored ℕ
> * Ball 2, colored ℕ
> * Ball 3, colored ℤ
> * Ball 4, colored ℕ

The equivalence becomes clearer if one thinks of constructing partitions by assigning group labels
(de Bruijn indices) to each ball, starting with 0, in accordance with the group we want each ball to
end up in. For example, one way to partition the balls into groups would be to make balls 1 and 4
form group 0, ball 2 form group 1, and ball 3 form group 2.

Now, it's important to note that `bvarChoices` does _not_ directly answer this question. However, it
is used (via `subsumersGo`) by `subsumers`, which _does_.

> Imagine someone having assigned ball 1 to group 0, ball 2 to group 1, and ball 3 to group 2, and
> now they have to decide what group label to assign to ball 4. Given that groups must be
> monochromatic, to give this person the list of possible group labels they may assign to ball 4, we
> need to know the colors of each existing group, and the color of ball 4. Since the groups are
> labeled 0, 1, 2, we can just store this information in an array `groupColors := #[ℕ, ℕ, ℤ]`, where
> we understand `groupColors[0]` to store the color of group 0, and so on. Now, if we also know the
> color of ball 4 — say, `color` — then we can compute the list of possible group labels.
>
> In this example, that list is `[0, 1, 3]`:
>
> * Assigning group label 0 to ball 4 would mean ball 4 joins ball 1 in group 0.
> * Assigning group label 1 to ball 4 would mean ball 4 joins ball 2 in group 1.
> * Note that group label 2 is not in the list, since group 2 is colored ℤ, not ℕ.
> * Assigning group label 3 to ball 4 would mean ball 4 starts a new group, namely group 3.
>
> Finally, instead of merely presenting the person with the list `[0, 1, 3]`, we decide to include,
> for each possible group label in the list, also the `groupColors` array that we would have if that
> group label were to be assigned to ball 4. That list looks like this:
>
> ```
> [
>   (0, #[ℕ, ℕ, ℤ]),
>   (1, #[ℕ, ℕ, ℤ]),
>   (3, #[ℕ, ℕ, ℤ, ℕ])
> ]
> ```

With this example, we have described what `bvarChoices #[ℕ, ℕ, ℤ] ℕ` does and returns. This also
answers the following question:

> If we want the first three arguments of `f ℕ ℕ ℤ ℕ` be abstracted to `.bvar 0`, `.bvar 1`, and
> `.bvar 2`, respectively, what may we abstract the fourth argument to, and what would be the
> resulting correspondence between bvar index and original argument value?

...with the following caveats:

* Ball $n$ corresponds to the $n$th argument of `f`.
* `groupColors` is actually called `bvarColors`.
* `ℕ` and `ℤ` are actually the expressions `.const `Nat []` and `.const `Int []`, respectively.
* The group labels 0, 1, 2, and 3 are actually the expressions `.bvar 0`, `.bvar 1`, `.bvar 2`, and
  `.bvar 3`, respectively.
* For the purposes of this docstring, leaving an argument as-is does not count as an abstraction.
-/
private def bvarChoices (bvarColors : Array Expr) (color : Expr) : List (Expr × Array Expr) :=
  (bvarColors.toList.zipIdx.filterMap fun (c, k) =>
    if c == color then some (.bvar k, bvarColors) else none)
  ++ [(.bvar bvarColors.size, bvarColors.push color)]


private partial def subsumersGo (bvarColors : Array Expr) : List Expr → List (Array Expr × Array Expr)
  | [] => [(#[], bvarColors)]
  | arg :: rest => (argSubsumersGo bvarColors arg).flatMap fun (arg', bvarColors') =>
      (subsumersGo bvarColors' rest).map fun (rest', bvarColors'') => (#[arg'] ++ rest', bvarColors'')
where
  argSubsumersGo (bvarColors : Array Expr) : Expr → List (Expr × Array Expr)
  | .bvar i => bvarChoices bvarColors (.bvar i)
  | color =>
    -- We can abstract the whole subterm, or
    bvarChoices bvarColors color ++ (
      -- if it isn't an application, we can choose to leave the term as-is, or,
      if color.getAppArgs.isEmpty then [(color, bvarColors)]
      -- if it _is_ an application, we can choose to keep the head, but abstract each argument.
      -- (Note that leaving an argument as-is would be considered a valid abstraction of said
      -- argument here.)
      else (subsumersGo bvarColors color.getAppArgs.toList).map fun (args, bvarColors') =>
        (mkAppN color.getAppFn args, bvarColors')
    )

open Lean Expr

/--
Given the arguments `#[a₁, …, aₙ]` of an application `f a₁ … aₙ`, returns an exhaustive list of all
the arrays `#[p₁, …, pₙ]` for which we have that `f p₁ … pₙ` subsumes `f a₁ … aₙ`.

---
**Example**

```
subsumers #[.bvar 3] = [#[.bvar 3]]
subsumers #[.lit 42] = [#[.bvar 0], #[42]]
subsumers #[.bvar 0, List (Nat × (.bvar 0)), .lit 42] = [
  #[#0, #1, #2]
  #[#0, #1, 42]
  #[#0, List #1, #2]
  #[#0, List #1, 42]
  #[#0, List (Prod #1 #0), #2]
  #[#0, List (Prod #1 #0), 42]
  #[#0, List (Prod #1 #2), #3]
  #[#0, List (Prod #1 #2), 42]
  #[#0, List (Prod Nat #0), #1]
  #[#0, List (Prod Nat #0), 42]
  #[#0, List (Prod Nat #1), #2]
  #[#0, List (Prod Nat #1), 42]
]
```
-/
private partial def subsumers (args : Array Expr) : List (Array Expr) :=
  (subsumersGo #[] args.toList).map (·.1)

/--
If `i ≤ 8`, then `bell[i]` is the `i`th Bell number. If `i > 8`, then `bell[i]` is `2³²`.

Mathematically speaking, the $i$th Bell number is the number of possible partitions of a set of $i$
elements.
-/
private def bell (n : Nat) : Nat := #[1, 1, 2, 5, 15, 52, 203, 877, 4140].getD n (1 <<< 32)

/--
The number of possible subsumers of an expression. If the expression is an application, then this
count is only accurate if every argument is (syntactically) different from every other argument,
otherwise it is a lower bound for the number of subsumers. (If an argument is itself an application,
then the arguments of that application also need to be (syntactically) different from every other
argument of that application, as well as from every argument of the parent application, for the
count to be accurate. And so on.)
-/
private partial def shapeCount : Expr → Nat
  | .bvar _ => 1
  | .lit _ => 2
  | e =>
    if e.getAppArgs.isEmpty then 2
    else 1 + e.getAppArgs.foldl (init := 1) fun shapeCount' arg => shapeCount' * shapeCount arg

/--
Walks `args` and counts multiplicities of colors, returning a map from colors to their
multiplicities. In other words, for a given expression `e`, the map will indicate how often `e`
occurs in `args` (be it as a top-level argument or an argument within an argument, etc.).
-/
private partial def colorMults (args : Array Expr) : HashMap Expr Nat :=
  args.foldl (init := {}) go
where
  go (colorMults' : HashMap Expr Nat) (arg : Expr) : HashMap Expr Nat :=
    arg.getAppArgs.foldl go (colorMults'.insert arg ((colorMults'.getD arg 0) + 1))

/--
An upper bound for how many subsumers `args` may have:

$$
  \prod_{\texttt{arg}\in\texttt{args}} \texttt{shapeCount}(\texttt{arg}) \cdot
  \prod_{\texttt{mult}\in\texttt{colorMults}(args)} \texttt{bell}(\texttt{mult})
  \geq |\texttt{subsumers}(\texttt{args})|
$$
-/
private def enumBudget (args : Array Expr) : Nat :=
  let shapes := args.foldl (init := 1) fun shapes' arg => shapes' * shapeCount arg
  let merges := (colorMults args).fold (init := 1) fun merges' _ k => merges' * bell k
  shapes * merges

/--
If the number of subsumers of `v.pattern` isn't estimated to exceed `maxCombined` (default 2048),
then all proper subsumers of `v.pattern` (i.e., subsumers of `v.pattern` that are not equal to
`v.pattern`) are returned as an array of vertices, where each output vertex `w` inherits all fields
from `v` except for `v.pattern`, which instead is set to the subsumer.
-/
public def Vertex.properSubsumers (v : Vertex) (maxCombined : Nat := 2048) : Array Vertex :=
  if enumBudget v.pattern > maxCombined then #[]
  else (subsumers v.pattern).foldl (init := #[]) fun out args =>
    if args == v.pattern then out
    else out.push { v with pattern := args }

/--
Given a vertex `query`, returns the array of vertices that match `query`. This is used to match
non-universe-polymorphic vertices with both the corresponding non-universe-polymorphic vertex _and_
the corresponding universe-polymorphic vertex.

If `includeSubsumers` is `true` (default `false`), then the query is extended to any subsuming
vertices.

---
**Examples**

* `Small.{0} α` will match `Small.{0} α` and `Small α` (the latter we understand to be
  universe-polymorphic).
* `Small.{123} α` will only match `Small α`, as there is no specific `Small.{123} α` vertex in the
  class graph.
-/
public def Vertex.matchingVertices (query : Vertex) (includeSubsumers : Bool := false) :
    Array Vertex :=
  let vertices := if includeSubsumers then #[query] ++ query.properSubsumers else #[query]
  vertices.flatMap fun v =>
    match v.levels with
    | .polymorphic => #[v]
    | .concrete _ => #[v, { v with levels := .polymorphic }]
