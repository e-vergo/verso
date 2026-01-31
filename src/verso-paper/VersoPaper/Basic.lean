/-
Copyright (c) 2025 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/
import Lean.Data.Json.FromToJson

import Std.Data.HashMap
import Std.Data.HashSet

import Verso.Doc
import Verso.Doc.Html
import Verso.Method

open Std (HashSet HashMap)
open Lean (Json ToJson FromJson Name)
open Verso Doc Output Html

namespace Verso.Genre

namespace Paper

/-!
# Paper Genre

A Verso genre for academic papers that can pull pre-built artifacts from manifest.json.
This allows writing papers in pure Verso markup with hooks like `:::paperstatement` and `:::paperfull`.
-/

/--
Configuration options for displaying Lean code in papers.
-/
structure CodeOpts where
  /-- Whether to show proof states in hovers -/
  showProofStates : Bool := true
  /-- Whether to show the proof body or just the statement -/
  showProof : Bool := true
deriving Repr, BEq, ToJson, FromJson

/--
The additional blocks available in papers.
-/
inductive BlockExt where
  /--
  Insert the LaTeX statement for a blueprint node, with a link to the Lean code.
  Usage: `:::paperStatement "thm:main"`
  -/
  | paperStatement (label : String)
  /--
  Insert the full side-by-side display for a blueprint node.
  Usage: `:::paperFull "thm:main"`
  -/
  | paperFull (label : String)
  /--
  Insert just the proof for a blueprint node.
  Usage: `:::paperProof "thm:main"`
  -/
  | paperProof (label : String)
  /--
  Insert a Lean node by label from the manifest.
  Usage: `:::leanNode "thm:main"`
  -/
  | leanNode (label : String)
  /--
  Insert all Lean nodes from a module.
  Usage: `:::leanModule "MyProject.Theorems"`
  -/
  | leanModule (moduleName : String)
  /--
  A wrapper div with custom classes.
  -/
  | htmlDiv (classes : String)
  /--
  A wrapper with a custom HTML tag.
  -/
  | htmlWrapper (tag : String) (attributes : Array (String × String))
deriving BEq, ToJson, FromJson

/--
The additional inline elements available in papers.
-/
inductive InlineExt where
  /--
  A reference to a blueprint node that creates a hyperlink.
  Usage: `{ref}`\`thm:main\``
  -/
  | nodeRef (label : String)
  /--
  Inline Lean code with highlighting.
  -/
  | leanCode (code : String)
  /--
  An HTML span element with the given classes.
  -/
  | htmlSpan (classes : String)
deriving BEq, ToJson, FromJson

section
local instance : Repr Json where
  reprPrec v := Repr.addAppParen <| "json%" ++ v.render

deriving instance Repr for BlockExt
deriving instance Repr for InlineExt
end

/--
Metadata for paper parts (sections, chapters, etc.)
-/
structure PartMetadata where
  /-- A shorter title to be shown in navigation -/
  shortTitle : Option String := none
  /-- Whether this section should be numbered -/
  number : Bool := true
  /-- The HTML ID to assign to the header -/
  htmlId : Option String := none
  /-- Whether to show this part in the table of contents -/
  showInToc : Bool := true
deriving Repr, BEq, ToJson, FromJson

/--
Configuration for paper generation.
-/
structure Config where
  /-- Output directory -/
  destination : System.FilePath := "./_site"
  /-- Path to manifest.json containing blueprint data -/
  manifestPath : Option System.FilePath := none
  /-- Base URL for links -/
  baseUrl : String := "/"
  /-- Paper title -/
  title : String := "Untitled Paper"
  /-- Paper authors -/
  authors : Array String := #[]
  /-- Paper abstract -/
  abstract : Option String := none
  /-- Error logging function -/
  logError : String → IO Unit
deriving Inhabited

/--
Traverse context for paper generation.
-/
structure TraverseContext where
  /-- Current path in the document tree -/
  path : Array String := #[]
  /-- Current configuration -/
  config : Config

/--
Traverse state for paper generation.
-/
structure TraverseState where
  /-- Used HTML IDs to ensure uniqueness -/
  usedIds : HashSet String := {}
  /-- Cross-reference targets: label -> path -/
  targets : HashMap String String := {}
  /-- Errors encountered during traversal -/
  errors : Array String := #[]

instance : BEq TraverseState where
  beq s1 s2 :=
    s1.usedIds.toList == s2.usedIds.toList &&
    s1.targets.toList == s2.targets.toList &&
    s1.errors == s2.errors

/--
The Paper genre for academic documents with blueprint integration.
-/
def Paper : Genre where
  PartMetadata := Paper.PartMetadata
  Block := Paper.BlockExt
  Inline := Paper.InlineExt
  TraverseContext := Paper.TraverseContext
  TraverseState := Paper.TraverseState

-- Type class instances for the Genre type aliases
-- Note: Genre.Block and Genre.Inline resolve to BlockExt and InlineExt respectively
instance : Repr (Genre.PartMetadata Paper) := inferInstanceAs (Repr PartMetadata)
instance : Repr (Genre.Block Paper) := inferInstanceAs (Repr BlockExt)
instance : Repr (Genre.Inline Paper) := inferInstanceAs (Repr InlineExt)

instance : BEq (Genre.PartMetadata Paper) := inferInstanceAs (BEq PartMetadata)
instance : BEq (Genre.Block Paper) := inferInstanceAs (BEq BlockExt)
instance : BEq (Genre.Inline Paper) := inferInstanceAs (BEq InlineExt)

instance : ToJson (Genre.PartMetadata Paper) := inferInstanceAs (ToJson PartMetadata)
instance : ToJson (Genre.Block Paper) := inferInstanceAs (ToJson BlockExt)
instance : ToJson (Genre.Inline Paper) := inferInstanceAs (ToJson InlineExt)

instance : FromJson (Genre.PartMetadata Paper) := inferInstanceAs (FromJson PartMetadata)
instance : FromJson (Genre.Block Paper) := inferInstanceAs (FromJson BlockExt)
instance : FromJson (Genre.Inline Paper) := inferInstanceAs (FromJson InlineExt)

/--
The traversal monad for paper generation.
-/
abbrev TraverseM := ReaderT TraverseContext (StateT TraverseState IO)

end Paper

end Verso.Genre
