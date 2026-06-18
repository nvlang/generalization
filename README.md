# Generalization linter

## Architecture

## Examples: Build time

### `extends`

The most common case.

```lean
-- Mathlib/Algebra/Group/Defs.lean:174-178
/-- A semigroup is a type with an associative `(*)`. -/
@[ext]
class Semigroup (G : Type u) extends Mul G where
  /-- Multiplication is associative -/
  protected mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
```

**✔ Edge:** `[Semigroup α] → [Mul α]`

**Questions:**
- _Should we care about the specific type universe in which the carrier resides?_ I don't think so; at build time, we canonicalize the carriers into a generic bvar anyway (losing their type info). Besides, I suspect the carriers will usually be universe-polymorphic anyway (though I should verify this still).


### Instance decl. with class application as output

```lean
-- Mathlib/Algebra/Group/Basic.lean:408-411
@[to_additive]
instance (priority := 100) DivisionMonoid.toDivInvOneMonoid : DivInvOneMonoid α :=
  { DivisionMonoid.toDivInvMonoid with
    inv_one := by simpa only [one_div, inv_inv] using (inv_div (1 : α) 1).symm }
```

**✔ Edge:** `[DivisionMonoid α] → [DivInvOneMonoid α]`

**Questions:**
- _Should we care about priority?_ I don't think we should, except in the specific case where we have a cluster of pairwise equivalent classes, in which case priority could help us pick which class to suggest from the cluster.


### Instance decl. with Prop as output

```lean
-- Mathlib/Algebra/Group/Basic.lean:58-59
@[to_additive]
instance Semigroup.to_isAssociative : Std.Associative (α := α) (· * ·) := ⟨mul_assoc⟩
```

**? Edge:** `[Semigroup α] → [Associative (· * ·)]` (?).

**Questions:**
- _Should we insert an edge? If so, what edge should we insert?_ It would seem that, whenever a theorem makes use of `[Associative (· * ·)]`, it'd also make use of `[Mul α]`, since it needs the `*` whose associativity it's using. But `[Mul α] [Associative (· * ·)]` is the same as `[Semigroup α]`, so a weakening from `[Semigroup α]` to `[Associative (· * ·)]` would never make sense. How could we detect a useless weakening like that?
  - #TODO
- _If we had e.g. `[Group α] [Group β] : ... := (proof that uses β's assoc, but not more for β)` and suggest replacing `[Group α] [Group β]` with `[Group α] [Mul β] [Associative (· * ·)]`, how do we know that `*` will refer to the operation from `Mul β`, and not that of `Group α`?_


### Instance decl. with ≥2 inst. implicit binders & class app. as output

A "hyperedge":

```lean
@[to_additive] instance (priority := low) (M) [MulOne M] [IsMulCommutative M] :
    IsDedekindFiniteMonoid M where
  mul_eq_one_symm := mul_comm' .. |>.trans
```

**? Edge:** `[IsMulCommutative M] → [IsDedekindFiniteMonoid M]` (?).

**Questions:**
- Should the edge be added?
  - **Pros:**
    - Suggestion candidates are verified before being emitted anyway, so adding this edge wouldn't compromise soundness, while potentially increasing recall.
    - Empirically, based on medium-scale experimentation (~thousands of decls), adding the edge yields a net increase in recall. This is low-quality evidence though.
  - **Cons:**
    - For theorems having `[IsMulCommutative M]` but not `[MulOne M]` (nor anything stronger) in their telescope, this edge could compete against other edges (edges which may actually be sound), thus potentially blocking a good suggestion candidate and instead pushing a bad suggestion candidate that then gets rejected by the verifier, reducing recall.
- Should the edge `[MulOne M] → [IsDedekindFiniteMonoid M]` also be added?
  - I think Claude argued against this, and ran some medium-scale experiments (~thousands of decls) that suggested adding this edge would lead to a net recall loss (and rarely if ever produce a new suggestion), which makes sense to me given the contra point from above. The experiments are low-quality evidence though.
- Should the edge `[MulOne M] → [IsDedekindFiniteMonoid M]` be added instead?
  - According to Claude, mathlib convention is that the last binder tends to be the "subject" of the declaration, whereas earlier binders tend to just be "setup". Claude argued that this means adding the edge `[IsMulCommutative M] → [IsDedekindFiniteMonoid M]` makes more sense than adding the edge `[MulOne M] → [IsDedekindFiniteMonoid M]`. This sounds reasonable to me, but might warrant further investigation.


### Instance decl. with inst. implicit binder & regular args, & class app. as output


## Examples: Run time

### Decidability questions

https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Order/Module/Defs.html#neg_of_smul_neg_right

```
theorem neg_of_smul_neg_right
    {α : Type u_1} {β : Type u_2} {a : α} {b : β}
    [Zero α] [Zero β] [SMulWithZero α β] 
    [Preorder α] [Preorder β] [SMulPosReflectLT α β] 
    (h : a • b < 0) (hb : 0 ≤ b) :
  a < 0
```

**Linter suggestion** (at some point pre-rewrite):

```
[LinearOrder β] ↝ [Preorder β]
    ⚠ This weakening drops [LinearOrder β]; `decide`/`native_decide`/`omega` may stop working downstream. Re-check before applying.
```

**Questions:**
- _How should matters of decidability be dealt with?_ #TODO: I haven't looked into this at all, and I don't really even know what decidability is referring to here.


### Artificial example showing why verification is necessary, even if DAG is fully sound

```lean
class A (α : Type) where a : α → α
class A' (α : Type) extends A α where a' : α → α
class B (α : Type) where b : α → α
class B' (α : Type) extends B α where b' : α → α

class C (α : Type) where c : α → α

instance A'B.toC [A' α] [B α] : C α := ⟨fun x => A'.a' x⟩
instance AB'.toC [A α] [B' α] : C α := ⟨fun x => B'.b' x⟩

theorem diamond {α : Type} [A' α] [B' α] (x : α) :
    A.a x = A.a x ∧ B.b x = B.b x ∧ C.c x = C.c x :=
  ⟨rfl, rfl, rfl⟩
```

DAG is just `A' -> A` and `B' -> B`, and the two instances `A'B.toC` and `AB'.toC` aren't inserted into the DAG (at least not in this hypothetical), since they're hyperedges. So the linter sees that `A'` could be weakened to `A`, and that `B'` could be weakened to `B`, and suggests both at the same time, not realizing that this compromises the theorem's reliance on `C`.

**Note:** If I recall, the real-world example that demonstrated this issue was very complex, and so simplifying it to a minimal demonstration made sense.

**Note:** Individually, the weakenings `A' -> A` and `B' -> B` are fine, so the linter should, ideally, just pick one and emit it. I got Claude to implement a "contextual" check to make the linter aware of these kinds of hyperedges (via `synthInst`) and hence able to act appropriately in this example. However, it's gated behind a default-off option, since it requires extra `synthInst` calls and hence slows down the linter. The slowdown isn't that great though, so I might want to look into making it a default-on option in the end — I'd have to run the numbers more thoroughly.



## Suspicious edge cases

These are declarations where the linter yielded odd suggestions.

### `Sum.instIsWellOrderLex`

https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Sum/Order.html#Sum.instIsWellOrderLex

```lean
instance Sum.instIsWellOrderLex 
    {α : Type u_1} {β : Type u_2} 
    (r : α → α → Prop) (s : β → β → Prop) 
    [IsWellOrder α r] [IsWellOrder β s] :
  IsWellOrder (α ⊕ β) (Lex r s)
```

**Linter suggestion** (at some point pre-rewrite):

```
[IsWellOrder α β] ↝ [IsWellFounded α β] [Std.Trichotomous α]
[IsWellOrder β β] ↝ [IsWellFounded β β] [Std.Trichotomous β]
```

**Why is this suspicious:**
- Why is the linter emitting a suggestion to weaken `[IsWellOrder β β]`, when that doesn't even appear in the declaration's telescope?
- Are we sure we want the linter to run on instance declarations?

### `InitialSeg.eq_or_principal`

https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/InitialSeg.html#InitialSeg.eq_or_principal

```lean
theorem InitialSeg.eq_or_principal 
    {α : Type u_1} {β : Type u_2} 
    {r : α → α → Prop} {s : β → β → Prop} 
    [IsWellOrder β s] (f : InitialSeg r s) :
  Function.Surjective ⇑f ∨ 
    ∃ (b : β), ∀ (x : β), x ∈ Set.range ⇑f ↔ s x b
```

**Linter suggestion** (at some point pre-rewrite):

```
[IsWellOrder β β] ↝ [IsWellFounded β β] [Std.Trichotomous β]
```

**Why is this suspicious:**
- Same as in `Sum.instIsWellOrderLex`: Why is the linter emitting a suggestion to weaken `[IsWellOrder β β]`, when that doesn't even appear in the declaration's telescope?


## Well-handled edge cases

### `Prod.swap_covBy_swap`

https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Cover.html#Prod.swap_covBy_swap

```lean
theorem Prod.swap_covBy_swap 
    {α : Type u_1} {β : Type u_2} 
    [PartialOrder α] [PartialOrder β] 
    {x y : α × β} :
  x.swap ⋖ y.swap ↔ x ⋖ y
```

**Linter suggestion** (at some point pre-rewrite):

```
[PartialOrder α] ↝ [Preorder α]
[PartialOrder β] ↝ [Preorder β]
```

**Why this is well-handled:**
- Being able to suggest two weakenings which are only differentiated by the carrier type is nice.

