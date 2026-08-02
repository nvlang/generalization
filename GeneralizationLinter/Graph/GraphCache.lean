/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
module

import Lean.Meta.Basic
import Lean.Meta.Instances
import Lean.Meta.FunInfo

public import GeneralizationLinter.Graph.ClassGraph

namespace GeneralizationLinter

open Lean Meta
open Std (HashSet)

/-! # Class graph cache -/

/-
Allocate storage for the result of `ClassGraph.scanInstances` on the imported instances, keyed by a
digest of the names it scanned. `attribute [instance]`/`[-instance]` on an imported constant, and
`open scoped`/`end` on an imported scoped instance, both change that set. Object identity is no use
here, unlike in `sameInstanceSet`: the array is rebuilt on every graph build.
-/
initialize importedScanRef :
    IO.Ref (Option (UInt64 × Array ClassEdge × HashSet Name)) ← IO.mkRef none


/-- Allocate storage for the cached `ClassGraph` and the instance set it was built from. -/
initialize classGraphCacheRef :
    IO.Ref (Option (PHashMap Name Meta.InstanceEntry × ClassGraph)) ← IO.mkRef none


/-
Allocate storage for the `assemble` result of the case where nothing local contributes, keyed by
`importedKey`. The graph is then a pure function of the imported scan, so reuse is exact.
-/
initialize importedOnlyGraphRef : IO.Ref (Option (UInt64 × ClassGraph)) ← IO.mkRef none


/-- For debugging: counts how many times `cachedClassGraph` has rebuilt the graph. -/
initialize graphBuildCountRef : IO.Ref Nat ← IO.mkRef 0


private unsafe def sameInstanceSetImpl (a b : PHashMap Name Meta.InstanceEntry) : Bool := ptrEq a b

/-
Do `a` and `b` denote the same instance set? Object identity is exact here: the map is persistent, so
any change allocates a new one, and the cached graph keeps its map alive. A spurious `false` costs a
rebuild, never soundness. Hashing the contents instead is a fold over ~40k entries, measured at 72ms
per declaration.
-/
@[implemented_by sameInstanceSetImpl]
private def sameInstanceSet (_a _b : PHashMap Name Meta.InstanceEntry) : Bool := false


/-
Digest of an imported instance set. `xor` rather than `mixHash`, so it does not depend on the order
the names came out of the instance map.
-/
private def importedKey (imported : Array Name) : UInt64 :=
  mixHash (hash imported.size) (imported.foldl (init := 0) fun h n => h ^^^ hash n)


/-
Scan the `imported` instances and record the result in `importedScanRef` under their `importedKey`.
-/
private def scanImported (imported : Array Name) : MetaM (Array ClassEdge × HashSet Name) := do
  let scan ← ClassGraph.scanInstances imported
  importedScanRef.set (some (importedKey imported, scan.1, scan.2))
  return scan


/-- Cached class graph. -/
public def cachedClassGraph : MetaM ClassGraph := do
  let env ← getEnv
  let instances := (instanceExtension.getState env).instanceNames
  if let some (instances', G) := ← classGraphCacheRef.get then
    if sameInstanceSet instances' instances then return G
  -- Only instances can produce edges. We enforce this restriction because the linter targets
  -- non-explicit binders for weakening, and non-explicit binders are resolved either using instance
  -- synthesis, or unification with instance synthesis as a fallback. So, when we analyze a
  -- declaration, we know that the current binder could be resolved, and we need to make sure that
  -- the weakened version we suggest can also be resolved, which is guaranteed (-ish) when there's a
  -- path in the class graph from the stronger to the weaker class, precisely because each edge of
  -- the class graph corresponds to an instance that instance synthesis can actually make use of.
  -- The expensive stuff: Scan imported environment.
  let imported := instances.foldl (init := (#[] : Array Name)) fun names name _ =>
    -- Filter out local constants.
    if env.constants.map₂.contains name then names else names.push name
  let (importedEdges, importedSubHeads) ← do
    -- reuse the previous scan only if the imported instance set is unchanged
    if let some (key, edges, subHeads) := ← importedScanRef.get then
      if key == importedKey imported then pure (edges, subHeads) else scanImported imported
    else scanImported imported
  -- The less expensive stuff: Scan local environment.
  let localNames := env.constants.map₂.foldl (init := (#[] : Array Name)) fun names name _ =>
    -- Filter out constants that aren't instances.
    if instances.contains name then names.push name else names
  let (localEdges, localSubHeads) ← ClassGraph.scanInstances localNames
  -- Nothing local contributes: no local edge, and no subsingleton head the imported scan did not
  -- already carry. Then `assemble`'s inputs are exactly the imported ones, so its result is a pure
  -- function of `importedKey` and the previously assembled graph is still right.
  let importedOnly := localEdges.isEmpty
    && localSubHeads.fold (init := true) fun acc h => acc && importedSubHeads.contains h
  if importedOnly then
    if let some (key, G) := ← importedOnlyGraphRef.get then
      if key == importedKey imported then
        classGraphCacheRef.set (some (instances, G))
        return G
  let G ← ClassGraph.assemble (importedEdges ++ localEdges)
    (localSubHeads.fold (init := importedSubHeads) (·.insert ·))
  if importedOnly then importedOnlyGraphRef.set (some (importedKey imported, G))
  graphBuildCountRef.modify (· + 1)
  classGraphCacheRef.set (some (instances, G))
  return G
