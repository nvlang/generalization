/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
module

public import Std.Data.HashSet.Basic

namespace GeneralizationLinter

/-!
# Coalescence

Tiny helper module with two definitions, `coalesceWith` and `coalesce`. In our
use case, these are used to transform very granular partitions into coarser
ones.
-/

namespace Coalescence

variable {α : Type _} [Inhabited α]

/--
Given an array `xs` and methods

* `fuse` to merge two elements of the array and
* `connected` to query whether two elements of the array should be merged (must
  be symmetric relation),

returns an array in which no two elements should be merged anymore.

---
**Examples:**

```
coalesceWith (·.append ·) (fun x y : List Nat => x.any y.contains)
  #[[1], [1, 2], [3], [2, 4], [5, 6]] = #[[1, 1, 2, 2, 4], [3], [5, 6]]
coalesceWith (·.union ·) (fun x y : Std.HashSet Nat => !(x.inter y).isEmpty)
  #[{1}, {1, 2}, {3}, {2, 4}, {5, 6}] = #[{1, 2, 4}, {3}, {5, 6}]
```
-/
public def coalesceWith (fuse : α → α → α) (connected : α → α → Bool)
    (xs : Array α) : Array α :=
  let rec loop (xs : Array α) (fuel : Nat) : Array α :=
    match fuel with
    | 0 => xs
    | fuel + 1 =>
      let fused : Option (Array α) := Id.run do
        for i in [0:xs.size] do
          for j in [i+1:xs.size] do
            if connected xs[i]! xs[j]! then
              return some (
                #[fuse xs[i]! xs[j]!] ++ ((xs.eraseIdxIfInBounds j).eraseIdxIfInBounds i)
              )
        return none
      match fused with
      | none => xs
      | some xs' => loop xs' fuel
  loop xs (xs.size * xs.size + 1)

public def coalesce [BEq α] [Hashable α] (connected : Std.HashSet α → Std.HashSet α → Bool)
    (blocks : Array (Std.HashSet α)) : Array (Std.HashSet α) :=
  coalesceWith (·.union ·) connected blocks
