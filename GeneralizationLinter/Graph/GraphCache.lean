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

/--
Allocate storage for the result of `ClassGraph.scanInstances` on the imported instances, keyed by
the number of instances that were imported when it was computed. Without a key the scan would
outlive the instance set it describes: `attribute [instance]`/`[-instance]` on an imported constant,
and `open scoped`/`end` activating or deactivating an imported scoped instance, all change which
imported instances synthesis can use.
-/
initialize importedScanRef : IO.Ref (Option (Nat × Array ClassEdge × HashSet Name)) ← IO.mkRef none


/-- Allocate storage for the cached `ClassGraph`. -/
initialize classGraphCacheRef : IO.Ref (Option (UInt64 × ClassGraph)) ← IO.mkRef none


/-- For debugging: counts how many times `cachedClassGraph` has rebuilt the graph. -/
initialize graphBuildCountRef : IO.Ref Nat ← IO.mkRef 0


/--
Compute fingerprint of the instances available for synthesis, for cache invalidation.

The fold covers local instance declarations. `instanceNames.size` is mixed in on top of it because
the fold alone is blind to anything that changes the *imported* half of the instance set:
`attribute [instance]`/`[-instance]` on an imported constant, and `open scoped`/`end` activating or
deactivating an imported scoped instance, all move the cardinality while leaving the fold's value
untouched. Only an exactly-compensating add-and-remove escapes both.
-/
public def localInstanceFingerprint : MetaM UInt64 := do
  let env ← getEnv
  let instances := (instanceExtension.getState env).instanceNames
  let local' := env.constants.map₂.foldl (init := (7 : UInt64)) fun h name const =>
    -- `name` is the name of a local constant, and `const` is the `ConstantInfo` associated with it.
    if instances.contains name then mixHash h (mixHash name.hash const.type.hash) else h
  -- `PHashMap` has no O(1) size, so this is a fold; it is one cheap pass over ~40k names
  let count := instances.foldl (init := 0) fun (n : Nat) _ _ => n + 1
  return mixHash local' (hash count)


/-- Cached class graph. -/
private def scanImported (imported : Array Name) :
    MetaM (Array ClassEdge × HashSet Name) := do
  let scan ← ClassGraph.scanInstances imported
  importedScanRef.set (some (imported.size, scan.1, scan.2))
  return scan


public def cachedClassGraph : MetaM ClassGraph := do
  let fp ← localInstanceFingerprint
  if let some (fp', G) := ← classGraphCacheRef.get then
    if fp' == fp then return G
  let env ← getEnv
  -- Only instances can produce edges. We enforce this restriction because the linter targets
  -- non-explicit binders for weakening, and non-explicit binders are resolved either using instance
  -- synthesis, or unification with instance synthesis as a fallback. So, when we analyze a
  -- declaration, we know that the current binder could be resolved, and we need to make sure that
  -- the weakened version we suggest can also be resolved, which is guaranteed (-ish) when there's a
  -- path in the class graph from the stronger to the weaker class, precisely because each edge of
  -- the class graph corresponds to an instance that instance synthesis can actually make use of.
  let instances := (instanceExtension.getState env).instanceNames
  -- The expensive stuff: Scan imported environment.
  let imported := instances.foldl (init := (#[] : Array Name)) fun names name _ =>
    -- Filter out local constants.
    if env.constants.map₂.contains name then names else names.push name
  let (importedEdges, importedSubHeads) ← do
    -- reuse the previous scan only if the imported instance set is still the same size
    if let some (n, edges, subHeads) := ← importedScanRef.get then
      if n == imported.size then pure (edges, subHeads) else scanImported imported
    else scanImported imported
  -- The less expensive stuff: Scan local environment.
  let localNames := env.constants.map₂.foldl (init := (#[] : Array Name)) fun names name _ =>
    -- Filter out constants that aren't instances.
    if instances.contains name then names.push name else names
  let (localEdges, localSubHeads) ← ClassGraph.scanInstances localNames
  let G ← ClassGraph.assemble (importedEdges ++ localEdges)
    (localSubHeads.fold (init := importedSubHeads) (·.insert ·))
  graphBuildCountRef.modify (· + 1)
  classGraphCacheRef.set (some (fp, G))
  return G
