/-
Copyright (c) 2025 Side-by-Side Blueprint Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Data.Json.FromToJson
import Lean.Data.Json.Parser
import Lean.Environment
import Std.Data.HashMap

/-!
# Manifest Types and Loading for SBSBlueprint

This module provides types for loading and working with `manifest.json` files generated
by Dress during the blueprint build process. The manifest contains:

- Node information (labels, URLs, status)
- Edge relationships (dependency graph)
- Status counts (for dashboard)
- Project notes and key declarations

## Caching

The manifest is cached using an environment extension to avoid repeated file reads
during elaboration. The cache is keyed by the manifest file path.

## Usage

```lean
-- Load manifest from the standard location
let manifest? ← loadManifest

-- Find a specific node
match manifest?.bind (·.findNode? "thm:main") with
| some node => ...
| none => ...
```
-/

namespace Verso.Genre.SBSBlueprint.Manifest

open Lean in
/--
Status counts from the manifest for dashboard display.
Matches the structure in manifest.json stats field.
-/
structure StatusCounts where
  /-- Total number of declarations -/
  total : Nat := 0
  /-- Nodes not ready for formalization -/
  notReady : Nat := 0
  /-- Nodes ready for formalization -/
  ready : Nat := 0
  /-- Nodes with sorry in proof -/
  hasSorry : Nat := 0
  /-- Nodes with complete proof -/
  proven : Nat := 0
  /-- Nodes where all dependencies are also fully proven -/
  fullyProven : Nat := 0
  /-- Nodes ready for mathlib submission -/
  mathlibReady : Nat := 0
  deriving Repr, BEq, Inhabited

open Lean in
instance : Lean.FromJson StatusCounts where
  fromJson? j := do
    let total := (j.getObjValAs? Nat "total").toOption.getD 0
    let notReady := (j.getObjValAs? Nat "notReady").toOption.getD 0
    let ready := (j.getObjValAs? Nat "ready").toOption.getD 0
    let hasSorry := (j.getObjValAs? Nat "hasSorry").toOption.getD 0
    let proven := (j.getObjValAs? Nat "proven").toOption.getD 0
    let fullyProven := (j.getObjValAs? Nat "fullyProven").toOption.getD 0
    let mathlibReady := (j.getObjValAs? Nat "mathlibReady").toOption.getD 0
    pure { total, notReady, ready, hasSorry, proven, fullyProven, mathlibReady }

open Lean in
instance : Lean.ToJson StatusCounts where
  toJson sc := Lean.Json.mkObj [
    ("total", Lean.ToJson.toJson sc.total),
    ("notReady", Lean.ToJson.toJson sc.notReady),
    ("ready", Lean.ToJson.toJson sc.ready),
    ("hasSorry", Lean.ToJson.toJson sc.hasSorry),
    ("proven", Lean.ToJson.toJson sc.proven),
    ("fullyProven", Lean.ToJson.toJson sc.fullyProven),
    ("mathlibReady", Lean.ToJson.toJson sc.mathlibReady)
  ]

/--
Validation check results from graph analysis.
-/
structure CheckResults where
  /-- Whether the graph is fully connected (single component) -/
  isConnected : Bool := true
  /-- Number of connected components -/
  numComponents : Nat := 1
  /-- Sizes of each connected component -/
  componentSizes : Array Nat := #[]
  /-- Detected cycles (as arrays of labels) -/
  cycles : Array (Array String) := #[]
  deriving Repr, BEq, Inhabited

open Lean in
instance : Lean.FromJson CheckResults where
  fromJson? j := do
    let isConnected := (j.getObjValAs? Bool "isConnected").toOption.getD true
    let numComponents := (j.getObjValAs? Nat "numComponents").toOption.getD 1
    let componentSizes := (j.getObjValAs? (Array Nat) "componentSizes").toOption.getD #[]
    let cycles := (j.getObjValAs? (Array (Array String)) "cycles").toOption.getD #[]
    pure { isConnected, numComponents, componentSizes, cycles }

open Lean in
instance : Lean.ToJson CheckResults where
  toJson cr := Lean.Json.mkObj [
    ("isConnected", Lean.ToJson.toJson cr.isConnected),
    ("numComponents", Lean.ToJson.toJson cr.numComponents),
    ("componentSizes", Lean.ToJson.toJson cr.componentSizes),
    ("cycles", Lean.ToJson.toJson cr.cycles)
  ]

/--
A project note item (label, id, and content).
-/
structure NoteItem where
  label : String
  id : String
  content : String
  deriving Repr, BEq, Inhabited

/--
Project notes from @[blueprint] attributes.
-/
structure ProjectNotes where
  /-- Priority items (id, label) -/
  priority : Array NoteItem := #[]
  /-- Blocked items with reasons -/
  blocked : Array NoteItem := #[]
  /-- Potential issues -/
  potentialIssues : Array NoteItem := #[]
  /-- Technical debt notes -/
  technicalDebt : Array NoteItem := #[]
  /-- Miscellaneous notes -/
  misc : Array NoteItem := #[]
  deriving Repr, BEq, Inhabited

open Lean in
private def parseNoteArray (j : Lean.Json) (contentField : String) : Array NoteItem := Id.run do
  match j with
  | .arr items =>
    let mut result : Array NoteItem := #[]
    for item in items do
      let label := (item.getObjValAs? String "label").toOption.getD ""
      let id := (item.getObjValAs? String "id").toOption.getD ""
      let content := (item.getObjValAs? String contentField).toOption.getD ""
      result := result.push { label, id, content }
    result
  | _ => #[]

open Lean in
instance : Lean.FromJson ProjectNotes where
  fromJson? j := do
    let priority := match j.getObjVal? "priority" with
      | .ok arr => parseNoteArray arr "priority"
      | .error _ => #[]
    let blocked := match j.getObjVal? "blocked" with
      | .ok arr => parseNoteArray arr "reason"
      | .error _ => #[]
    let potentialIssues := match j.getObjVal? "potentialIssues" with
      | .ok arr => parseNoteArray arr "issue"
      | .error _ => #[]
    let technicalDebt := match j.getObjVal? "technicalDebt" with
      | .ok arr => parseNoteArray arr "debt"
      | .error _ => #[]
    let misc := match j.getObjVal? "misc" with
      | .ok arr => parseNoteArray arr "note"
      | .error _ => #[]
    pure { priority, blocked, potentialIssues, technicalDebt, misc }

open Lean in
instance : Lean.ToJson ProjectNotes where
  toJson pn := Lean.Json.mkObj [
    ("priority", Lean.ToJson.toJson (pn.priority.map fun n => Lean.Json.mkObj [
      ("label", Lean.ToJson.toJson n.label),
      ("id", Lean.ToJson.toJson n.id)
    ])),
    ("blocked", Lean.ToJson.toJson (pn.blocked.map fun n => Lean.Json.mkObj [
      ("label", Lean.ToJson.toJson n.label),
      ("id", Lean.ToJson.toJson n.id),
      ("reason", Lean.ToJson.toJson n.content)
    ])),
    ("potentialIssues", Lean.ToJson.toJson (pn.potentialIssues.map fun n => Lean.Json.mkObj [
      ("label", Lean.ToJson.toJson n.label),
      ("id", Lean.ToJson.toJson n.id),
      ("issue", Lean.ToJson.toJson n.content)
    ])),
    ("technicalDebt", Lean.ToJson.toJson (pn.technicalDebt.map fun n => Lean.Json.mkObj [
      ("label", Lean.ToJson.toJson n.label),
      ("id", Lean.ToJson.toJson n.id),
      ("debt", Lean.ToJson.toJson n.content)
    ])),
    ("misc", Lean.ToJson.toJson (pn.misc.map fun n => Lean.Json.mkObj [
      ("label", Lean.ToJson.toJson n.label),
      ("id", Lean.ToJson.toJson n.id),
      ("note", Lean.ToJson.toJson n.content)
    ]))
  ]

/--
A message associated with a node.
-/
structure MessageItem where
  id : String
  label : String
  message : String
  deriving Repr, BEq, Inhabited

open Lean in
instance : Lean.FromJson MessageItem where
  fromJson? j := do
    let id ← j.getObjValAs? String "id"
    let label := (j.getObjValAs? String "label").toOption.getD ""
    let message ← j.getObjValAs? String "message"
    pure { id, label, message }

open Lean in
instance : Lean.ToJson MessageItem where
  toJson m := Lean.Json.mkObj [
    ("id", Lean.ToJson.toJson m.id),
    ("label", Lean.ToJson.toJson m.label),
    ("message", Lean.ToJson.toJson m.message)
  ]

/--
Node information from the manifest.
The manifest stores nodes as an object mapping id to URL.
-/
structure NodeInfo where
  /-- Node identifier (e.g., "thm:main") -/
  id : String
  /-- URL fragment for this node (e.g., "#thm:main") -/
  url : String
  deriving Repr, BEq, Inhabited, Hashable

/--
Edge information representing a dependency between nodes.
-/
structure EdgeInfo where
  /-- Source node id -/
  source : String
  /-- Target node id -/
  target : String
  /-- Whether this is a statement dependency (vs proof dependency) -/
  isStatement : Bool := false
  deriving Repr, BEq, Inhabited

/--
The complete manifest loaded from manifest.json.
Contains node URLs, statistics, and validation results.

Note: The manifest.json format from Dress stores nodes as an object
mapping id to URL, not as an array of full node details.
-/
structure BlueprintManifest where
  /-- Node id to URL mapping -/
  nodes : Std.HashMap String String := {}
  /-- Pre-computed status counts -/
  stats : StatusCounts := {}
  /-- Graph validation results -/
  checks : CheckResults := {}
  /-- Key declaration ids -/
  keyDeclarations : Array String := #[]
  /-- User messages from @[blueprint message := "..."] -/
  messages : Array MessageItem := #[]
  /-- Project notes for dashboard -/
  projectNotes : ProjectNotes := {}
  deriving Repr

instance : Inhabited BlueprintManifest where
  default := {}

open Lean in
instance : Lean.FromJson BlueprintManifest where
  fromJson? j := do
    -- Parse nodes (object mapping id to URL)
    let nodes : Std.HashMap String String := match j.getObjVal? "nodes" with
      | .ok (.obj entries) =>
        entries.toArray.foldl (init := {}) fun acc (id, urlJson) =>
          match urlJson.getStr? with
          | .ok url => acc.insert id url
          | .error _ => acc
      | _ => {}

    let stats := (j.getObjValAs? StatusCounts "stats").toOption.getD {}
    let checks := (j.getObjValAs? CheckResults "checks").toOption.getD {}
    let keyDeclarations := (j.getObjValAs? (Array String) "keyDeclarations").toOption.getD #[]
    let messages := (j.getObjValAs? (Array MessageItem) "messages").toOption.getD #[]
    let projectNotes := (j.getObjValAs? ProjectNotes "projectNotes").toOption.getD {}
    pure { nodes, stats, checks, keyDeclarations, messages, projectNotes }

open Lean in
instance : Lean.ToJson BlueprintManifest where
  toJson m := Lean.Json.mkObj [
    ("nodes", Lean.Json.mkObj (m.nodes.toArray.map fun (id, url) => (id, Lean.ToJson.toJson url)).toList),
    ("stats", Lean.ToJson.toJson m.stats),
    ("checks", Lean.ToJson.toJson m.checks),
    ("keyDeclarations", Lean.ToJson.toJson m.keyDeclarations),
    ("messages", Lean.ToJson.toJson m.messages),
    ("projectNotes", Lean.ToJson.toJson m.projectNotes)
  ]

/--
Find a node by its id in the manifest.
Returns the URL for the node if found.
-/
def BlueprintManifest.findNode? (m : BlueprintManifest) (id : String) : Option NodeInfo :=
  m.nodes.get? id |>.map fun url => { id, url }

/--
Find all nodes from a given module.
Note: The current manifest format doesn't include module information per node,
so this always returns an empty array. Full node details would need to be
loaded from individual artifact files.
-/
def BlueprintManifest.findNodesByModule (_m : BlueprintManifest) (_moduleName : String) : Array NodeInfo :=
  #[]  -- Module info not available in current manifest format

/--
Check if a node is a key declaration.
-/
def BlueprintManifest.isKeyDeclaration (m : BlueprintManifest) (id : String) : Bool :=
  m.keyDeclarations.contains id

/--
Get the message for a node, if any.
-/
def BlueprintManifest.getMessage (m : BlueprintManifest) (id : String) : Option String :=
  m.messages.find? (·.id == id) |>.map (·.message)

/--
Get all node ids in the manifest.
-/
def BlueprintManifest.nodeIds (m : BlueprintManifest) : Array String :=
  m.nodes.toArray.map (·.1)

/-!
## Manifest Loading and Caching

The manifest is loaded from disk and cached to avoid repeated file reads.
-/

/--
The default location for manifest.json relative to the project root.
-/
def defaultManifestPath : System.FilePath :=
  ".lake" / "build" / "dressed" / "manifest.json"

/--
Load a manifest from a JSON file.
-/
def BlueprintManifest.loadFromFile (path : System.FilePath) : IO BlueprintManifest := do
  let contents ← IO.FS.readFile path
  match Lean.Json.parse contents with
  | .error e => throw <| IO.userError s!"Failed to parse manifest JSON at {path}: {e}"
  | .ok json =>
    match Lean.FromJson.fromJson? json with
    | .error e => throw <| IO.userError s!"Failed to decode manifest at {path}: {e}"
    | .ok manifest => pure manifest

/--
Cached manifest data for the environment extension.
-/
structure ManifestCache where
  /-- Path to the manifest file -/
  path : System.FilePath
  /-- Loaded manifest data -/
  manifest : BlueprintManifest
  deriving Inhabited

/--
Environment extension for caching the manifest.
-/
initialize manifestCacheExt : Lean.EnvExtension (Option ManifestCache) ←
  Lean.registerEnvExtension (pure none)

/--
Load the manifest from the default location, using the cache if available.
Returns `none` if the manifest file doesn't exist.
-/
def loadManifest : IO (Option BlueprintManifest) := do
  let path := defaultManifestPath
  if ← path.pathExists then
    let manifest ← BlueprintManifest.loadFromFile path
    pure (some manifest)
  else
    pure none

/--
Load the manifest from a custom path, using the cache if available.
Returns `none` if the manifest file doesn't exist.
-/
def loadManifestFrom (path : System.FilePath) : IO (Option BlueprintManifest) := do
  if ← path.pathExists then
    let manifest ← BlueprintManifest.loadFromFile path
    pure (some manifest)
  else
    pure none

/--
Load manifest with caching in the Lean environment.
This is useful during elaboration to avoid repeated file reads.
-/
def loadManifestCached [Monad m] [Lean.MonadEnv m] [MonadLiftT IO m]
    (path : System.FilePath := defaultManifestPath) : m (Option BlueprintManifest) := do
  let env ← Lean.getEnv
  -- Check cache
  match manifestCacheExt.getState env with
  | some cache =>
    if cache.path == path then
      return some cache.manifest
    else
      -- Different path, reload
      loadAndCache path
  | none =>
    loadAndCache path
where
  loadAndCache (path : System.FilePath) : m (Option BlueprintManifest) := do
    let fileExists ← MonadLiftT.monadLift (path.pathExists : IO Bool)
    if fileExists then
      let manifest ← BlueprintManifest.loadFromFile path
      let cache : ManifestCache := { path, manifest }
      Lean.modifyEnv (manifestCacheExt.setState · (some cache))
      return some manifest
    else
      return none

end Verso.Genre.SBSBlueprint.Manifest
