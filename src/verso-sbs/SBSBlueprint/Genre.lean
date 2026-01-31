/-
Copyright (c) 2025 Side-by-Side Blueprint Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Data.Json.FromToJson
import Std.Data.HashMap
import Std.Data.HashSet

import Verso.Doc
import Verso.Doc.Html
import Verso.Output.Html
import Verso.Method

import SubVerso.Highlighting

/-!
# SBSBlueprint Genre Definition

This module defines the `SBSBlueprint` genre for Verso, enabling the creation of
mathematical blueprints that display formal Lean proofs alongside LaTeX theorem
statements.

## Overview

The genre provides:
- Extension types for blueprint-specific content (side-by-side displays, hooks)
- Metadata for tracking declaration status and relationships
- Traversal context/state for resolving cross-references

## Architecture

SBSBlueprint reuses components from the Blog genre for code highlighting since
they already integrate with SubVerso. The genre adds blueprint-specific extensions
for `\lean{}`, `\uses{}`, and side-by-side rendering.
-/

namespace Verso.Genre.SBSBlueprint

open Lean (Name Json ToJson FromJson)
open Std (HashMap HashSet)
open Verso Doc Output Html
open SubVerso.Highlighting

/-!
## Node Status

Status values for blueprint nodes, matching the existing 6-status color model.
-/

/--
Status of a blueprint node, determining its color in the dependency graph.
-/
inductive NodeStatus where
  | /-- Not ready for formalization (default, sandy brown) -/ notReady
  | /-- Ready to be formalized (manual, light sea green) -/ ready
  | /-- Proof contains sorry (auto-detected, dark red) -/ sorry
  | /-- Complete proof (auto-detected, light green) -/ proven
  | /-- Fully proven with all dependencies (auto-computed, forest green) -/ fullyProven
  | /-- Ready for mathlib submission (manual, light blue) -/ mathlibReady
  deriving Repr, BEq, Inhabited, DecidableEq, Hashable

/--
Convert NodeStatus to a string identifier.
-/
def NodeStatus.toIdent : NodeStatus → String
  | .notReady => "notReady"
  | .ready => "ready"
  | .sorry => "sorry"
  | .proven => "proven"
  | .fullyProven => "fullyProven"
  | .mathlibReady => "mathlibReady"

instance : ToString NodeStatus where
  toString := NodeStatus.toIdent

instance : ToJson NodeStatus where
  toJson s := Json.str s.toIdent

instance : FromJson NodeStatus where
  fromJson? j := do
    let s ← j.getStr?
    match s with
    | "notReady" | "stated" => pure .notReady  -- "stated" for backwards compat
    | "ready" => pure .ready
    | "sorry" => pure .sorry
    | "proven" => pure .proven
    | "fullyProven" => pure .fullyProven
    | "mathlibReady" | "inMathlib" => pure .mathlibReady  -- "inMathlib" for backwards compat
    | _ => throw s!"Unknown status: {s}"

/--
Get the CSS color for a node status.
-/
def NodeStatus.color : NodeStatus → String
  | .notReady => "#F4A460"     -- Sandy Brown
  | .ready => "#20B2AA"        -- Light Sea Green
  | .sorry => "#8B0000"        -- Dark Red
  | .proven => "#90EE90"       -- Light Green
  | .fullyProven => "#228B22"  -- Forest Green
  | .mathlibReady => "#87CEEB" -- Light Blue

/-!
## Block and Inline Extensions

Blueprint-specific extensions for document content.
-/

/--
Configuration options for code rendering.
-/
structure CodeOpts where
  /-- Context name for the code example -/
  contextName : Name
  /-- Whether to show proof states -/
  showProofStates : Bool := true
  deriving Repr, BEq, ToJson, FromJson

/--
Block-level extensions for blueprints.
-/
inductive BlockExt where
  /-- Highlighted Lean code block -/
  | highlightedCode (opts : CodeOpts) (highlighted : Highlighted)
  /-- Side-by-side display: LaTeX statement paired with Lean code -/
  | sideBySide
      (label : String)
      (latexContent : Html)
      (leanCode : Option Highlighted)
      (status : NodeStatus)
  /-- Theorem environment with optional proof -/
  | theoremEnv
      (kind : String)  -- "theorem", "lemma", "definition", etc.
      (label : String)
      (title : Option String)
      (statement : Html)
      (proof : Option Html)
  /-- Proof block that can be toggled -/
  | proofBlock (content : Html)
  /-- A div wrapper with CSS classes -/
  | htmlDiv (classes : String)
  /-- Hook: Full side-by-side display (statement + proof + Lean code) -/
  | leanNode (label : String)
  /-- Hook: Statement with Lean signature only -/
  | paperStatement (label : String)
  /-- Hook: Statement + proof + full Lean code -/
  | paperFull (label : String)
  /-- Hook: Proof body only -/
  | paperProof (label : String)
  /-- Hook: All nodes from a module -/
  | leanModule (moduleName : String)
  deriving Repr, BEq, ToJson, FromJson

/--
Inline-level extensions for blueprints.
-/
inductive InlineExt where
  /-- Highlighted inline Lean code -/
  | highlightedCode (opts : CodeOpts) (highlighted : Highlighted)
  /-- Reference to a blueprint node by label -/
  | nodeRef (label : String) (resolvedUrl : Option String := none)
  /-- Status indicator dot -/
  | statusDot (status : NodeStatus)
  /-- Link to Lean documentation -/
  | leanDocLink (declName : Name) (url : Option String := none)
  /-- An HTML span with classes -/
  | htmlSpan (classes : String)
  deriving Repr, BEq, ToJson, FromJson

/-!
## Part Metadata

Metadata associated with parts (chapters, sections) in a blueprint document.
-/

/--
Metadata for blueprint parts.
-/
structure BlueprintMetadata where
  /-- Unique identifier for cross-referencing -/
  id : Option String := none
  /-- Custom title (overrides auto-generated) -/
  title : Option String := none
  /-- Whether this is a key declaration (shown in dashboard) -/
  keyDeclaration : Bool := false
  /-- User message (shown in Messages panel) -/
  message : Option String := none
  /-- Whether this is a priority item (shown in Attention column) -/
  priorityItem : Bool := false
  /-- Blockage reason -/
  blocked : Option String := none
  /-- Known potential issues -/
  potentialIssue : Option String := none
  /-- Technical debt notes -/
  technicalDebt : Option String := none
  /-- Miscellaneous notes -/
  misc : Option String := none
  /-- Manual status override -/
  manualStatus : Option NodeStatus := none
  /-- Whether this part should be numbered -/
  number : Bool := true
  /-- HTML ID for the header -/
  htmlId : Option String := none
  deriving Repr, BEq, Inhabited

instance : ToJson BlueprintMetadata where
  toJson m := Json.mkObj [
    ("id", ToJson.toJson m.id),
    ("title", ToJson.toJson m.title),
    ("keyDeclaration", ToJson.toJson m.keyDeclaration),
    ("message", ToJson.toJson m.message),
    ("priorityItem", ToJson.toJson m.priorityItem),
    ("blocked", ToJson.toJson m.blocked),
    ("potentialIssue", ToJson.toJson m.potentialIssue),
    ("technicalDebt", ToJson.toJson m.technicalDebt),
    ("misc", ToJson.toJson m.misc),
    ("manualStatus", ToJson.toJson m.manualStatus),
    ("number", ToJson.toJson m.number),
    ("htmlId", ToJson.toJson m.htmlId)
  ]

instance : FromJson BlueprintMetadata where
  fromJson? j := do
    let id := (j.getObjValAs? String "id").toOption
    let title := (j.getObjValAs? String "title").toOption
    let keyDeclaration := (j.getObjValAs? Bool "keyDeclaration").toOption.getD false
    let message := (j.getObjValAs? String "message").toOption
    let priorityItem := (j.getObjValAs? Bool "priorityItem").toOption.getD false
    let blocked := (j.getObjValAs? String "blocked").toOption
    let potentialIssue := (j.getObjValAs? String "potentialIssue").toOption
    let technicalDebt := (j.getObjValAs? String "technicalDebt").toOption
    let misc := (j.getObjValAs? String "misc").toOption
    let manualStatus := (j.getObjValAs? NodeStatus "manualStatus").toOption
    let number := (j.getObjValAs? Bool "number").toOption.getD true
    let htmlId := (j.getObjValAs? String "htmlId").toOption
    pure {
      id, title, keyDeclaration, message, priorityItem,
      blocked, potentialIssue, technicalDebt, misc,
      manualStatus, number, htmlId
    }

/-!
## Traversal Context and State

Context and state used during the document traversal pass.
-/

/--
Read-only context available during traversal.
-/
structure TraverseContext where
  /-- Function for logging errors -/
  logError : String → IO Unit := fun _ => pure ()
  /-- Whether we're in draft mode -/
  draft : Bool := false
  /-- Base URL for the site -/
  baseUrl : String := "/"
  /-- Path to the current part in the document tree -/
  currentPath : Array String := #[]
  deriving Inhabited

/--
Mutable state accumulated during traversal.
-/
structure TraverseState where
  /-- Mapping from node labels to their URLs -/
  nodeUrls : HashMap String String := {}
  /-- Set of key declaration labels -/
  keyDeclarations : HashSet String := {}
  /-- Messages from nodes -/
  messages : Array (String × String × String) := #[]  -- (id, label, message)
  /-- Blocked items -/
  blocked : Array (String × String × String) := #[]  -- (id, label, reason)
  /-- Potential issues -/
  potentialIssues : Array (String × String × String) := #[]
  /-- Technical debt notes -/
  technicalDebt : Array (String × String × String) := #[]
  /-- Miscellaneous notes -/
  misc : Array (String × String × String) := #[]
  /-- Node statuses -/
  nodeStatuses : HashMap String NodeStatus := {}
  /-- Dependency edges (from -> to) -/
  edges : Array (String × String × Bool) := #[]  -- (from, to, isStatementDep)
  /-- Errors encountered during traversal -/
  errors : Array String := #[]
  deriving Inhabited

/--
Compare two HashMaps for equality using BEq.
-/
private def hashMapBEq [BEq α] [Hashable α] [BEq β] (m1 m2 : HashMap α β) : Bool :=
  m1.size == m2.size && m1.toArray.all fun (k, v) =>
    m2[k]? == some v

/--
Compare two HashSets for equality.
-/
private def hashSetBEq [BEq α] [Hashable α] (s1 s2 : HashSet α) : Bool :=
  s1.size == s2.size && s1.toArray.all s2.contains

instance : BEq TraverseState where
  beq s1 s2 :=
    hashMapBEq s1.nodeUrls s2.nodeUrls &&
    hashSetBEq s1.keyDeclarations s2.keyDeclarations &&
    s1.messages == s2.messages &&
    s1.blocked == s2.blocked &&
    s1.potentialIssues == s2.potentialIssues &&
    s1.technicalDebt == s2.technicalDebt &&
    s1.misc == s2.misc &&
    hashMapBEq s1.nodeStatuses s2.nodeStatuses &&
    s1.edges == s2.edges &&
    s1.errors == s2.errors

/-!
## Genre Definition

The SBSBlueprint genre itself.
-/

/--
The SBSBlueprint genre for mathematical formalization documents.

This genre enables side-by-side display of LaTeX theorem statements
paired with their Lean formalizations, with automatic status tracking
and dependency graph generation.
-/
def SBSBlueprint : Genre where
  PartMetadata := BlueprintMetadata
  Block := BlockExt
  Inline := InlineExt
  TraverseContext := TraverseContext
  TraverseState := TraverseState

/-!
## Traversal Monad

A convenience monad for traversal operations.
-/

/--
Monad for document traversal operations.
-/
abbrev TraverseM := ReaderT TraverseContext (StateT TraverseState IO)

/--
Log an error during traversal.
-/
def logTraverseError [Monad m] [MonadReader TraverseContext m] [MonadLiftT IO m]
    (msg : String) : m Unit := do
  (← read).logError msg

/--
Add an error to the traversal state.
-/
def addError [Monad m] [MonadState TraverseState m] (msg : String) : m Unit := do
  modify fun s => { s with errors := s.errors.push msg }

/--
Register a node URL in the traversal state.
-/
def registerNode [Monad m] [MonadState TraverseState m]
    (label : String) (url : String) : m Unit := do
  modify fun s => { s with nodeUrls := s.nodeUrls.insert label url }

/--
Register a key declaration.
-/
def registerKeyDeclaration [Monad m] [MonadState TraverseState m]
    (label : String) : m Unit := do
  modify fun s => { s with keyDeclarations := s.keyDeclarations.insert label }

/--
Register a dependency edge.
-/
def registerEdge [Monad m] [MonadState TraverseState m]
    (from_ to : String) (isStatement : Bool := false) : m Unit := do
  modify fun s => { s with edges := s.edges.push (from_, to, isStatement) }

/--
Look up a node URL.
-/
def lookupNode [Monad m] [MonadState TraverseState m]
    (label : String) : m (Option String) := do
  return (← get).nodeUrls[label]?

/-!
## Traverse Instances

Instances for the document traversal pass.
-/

instance : TraversePart SBSBlueprint where
  -- Default implementation

instance : TraverseBlock SBSBlueprint where
  -- Default implementation

instance : Traverse SBSBlueprint TraverseM where
  part _ := pure none
  block _ := pure ()
  inline _ := pure ()

  genrePart metadata _part := do
    -- Register the part if it has an ID
    if let some id := metadata.id then
      let path := (← read).currentPath
      let url := "/" ++ String.intercalate "/" path.toList ++ "#" ++ id
      registerNode id url

      -- Track key declarations
      if metadata.keyDeclaration then
        registerKeyDeclaration id

      -- Track messages
      if let some msg := metadata.message then
        modify fun s => { s with messages := s.messages.push (id, metadata.title.getD id, msg) }

      -- Track blocked items
      if let some reason := metadata.blocked then
        modify fun s => { s with blocked := s.blocked.push (id, metadata.title.getD id, reason) }

      -- Track potential issues
      if let some issue := metadata.potentialIssue then
        modify fun s => { s with potentialIssues := s.potentialIssues.push (id, metadata.title.getD id, issue) }

      -- Track technical debt
      if let some debt := metadata.technicalDebt then
        modify fun s => { s with technicalDebt := s.technicalDebt.push (id, metadata.title.getD id, debt) }

      -- Track misc notes
      if let some note := metadata.misc then
        modify fun s => { s with misc := s.misc.push (id, metadata.title.getD id, note) }

      -- Track manual status if provided
      if let some status := metadata.manualStatus then
        modify fun s => { s with nodeStatuses := s.nodeStatuses.insert id status }

    pure none

  genreBlock
    | .highlightedCode _ _, _ => pure none
    | .sideBySide label _ _ status, _ => do
        -- Register the node
        let path := (← read).currentPath
        let url := "/" ++ String.intercalate "/" path.toList ++ "#" ++ label
        registerNode label url
        -- Store status
        modify fun s => { s with nodeStatuses := s.nodeStatuses.insert label status }
        pure none
    | .theoremEnv _ label _ _ _, _ => do
        -- Register the node
        let path := (← read).currentPath
        let url := "/" ++ String.intercalate "/" path.toList ++ "#" ++ label
        registerNode label url
        pure none
    | .proofBlock _, _ => pure none
    | .htmlDiv _, _ => pure none
    | .leanNode label, _ => do
        -- Register the node for hooks
        let path := (← read).currentPath
        let url := "/" ++ String.intercalate "/" path.toList ++ "#" ++ label
        registerNode label url
        pure none
    | .paperStatement label, _ => do
        let path := (← read).currentPath
        let url := "/" ++ String.intercalate "/" path.toList ++ "#" ++ label
        registerNode label url
        pure none
    | .paperFull label, _ => do
        let path := (← read).currentPath
        let url := "/" ++ String.intercalate "/" path.toList ++ "#" ++ label
        registerNode label url
        pure none
    | .paperProof label, _ => do
        let path := (← read).currentPath
        let url := "/" ++ String.intercalate "/" path.toList ++ "#" ++ label
        registerNode label url
        pure none
    | .leanModule _, _ => pure none  -- Module hooks don't register individual nodes

  genreInline
    | .highlightedCode _ _, _ => pure none
    | .nodeRef label none, contents => do
        -- Try to resolve the reference
        let resolved ← lookupNode label
        if resolved.isSome then
          pure (some (.other (.nodeRef label resolved) contents))
        else
          pure none
    | .nodeRef _ (some _), _ => pure none  -- Already resolved
    | .statusDot _, _ => pure none
    | .leanDocLink _ _, _ => pure none
    | .htmlSpan _, _ => pure none

/-!
## HTML Generation

The GenreHtml instance is defined in Render.lean, which has access to
the RenderContext needed for loading artifacts and manifest data.
-/

end Verso.Genre.SBSBlueprint
