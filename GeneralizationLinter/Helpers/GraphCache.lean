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
public import GeneralizationLinter.Helpers.ClassGraph

namespace GeneralizationLinter

open Lean Meta
open Std (HashSet)

/-! # Class graph cache -/

/-- Allocate storage for the result of `ClassGraph.scanInstances` on the imported instances. -/
initialize importedScanRef : IO.Ref (Option (Array ClassEdge × HashSet Name)) ← IO.mkRef none

/-- Allocate storage for the cached `ClassGraph`. -/
initialize classGraphCacheRef : IO.Ref (Option (UInt64 × ClassGraph)) ← IO.mkRef none

/-- For debugging. -/
initialize graphBuildCountRef : IO.Ref Nat ← IO.mkRef 0

/-- Compute fingerprint of local instance declarations, for cache invalidation. -/
public def localInstanceFingerprint : MetaM UInt64 := do
  let env ← getEnv
  let instances := (instanceExtension.getState env).instanceNames
  return env.constants.map₂.foldl (init := (7 : UInt64)) fun h name const =>
    -- `name` is the name of a local instance, and `const` is the `ConstantInfo` associated with it.
    if instances.contains name then mixHash h (mixHash name.hash const.type.hash) else h

/-- Cached class graph. -/
public def cachedClassGraph : MetaM ClassGraph := do
  let fp ← localInstanceFingerprint
  if let some (fp', G) := ← classGraphCacheRef.get then
    if fp' == fp then return G
  let env ← getEnv
  let instances := (instanceExtension.getState env).instanceNames
  -- The expensive stuff: Scan imported environment.
  let (importedEdges, importedSubHeads) ← (← importedScanRef.get).getDM do
    let imported := instances.foldl (init := (#[] : Array Name)) fun names name _ =>
      -- Filter out local constants.
      if env.constants.map₂.contains name then names else names.push name
    let scan ← ClassGraph.scanInstances imported
    importedScanRef.set (some scan)
    return scan
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
