/-
Copyright (c) 2025 Side-by-Side Blueprint Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

-- Core Verso imports
import Verso.Doc
import Verso.Doc.Concrete
import Verso.Doc.Html
import Verso.Doc.Elab
import Verso.Output.Html
import Verso.FS

-- SubVerso for code highlighting
import SubVerso.Highlighting

-- Submodules
import SBSBlueprint.Genre
import SBSBlueprint.Hooks
import SBSBlueprint.Manifest
import SBSBlueprint.Render

/-!
# SBSBlueprint: Side-by-Side Blueprint Genre for Verso

This module provides a Verso genre for writing mathematical blueprints that display
formal Lean proofs alongside LaTeX theorem statements. The genre enables compile-time
resolution of blueprint hooks (like `\lean{}` and `\uses{}`), eliminating the need for
a separate LaTeX parsing pass.

## Key Features

- **Side-by-side display**: LaTeX statements paired with Lean formalizations
- **Compile-time hook resolution**: `\lean{}` hooks resolved during Lean elaboration
- **Dependency tracking**: `\uses{}` relationships captured in the manifest
- **Status computation**: Automatic status (proven, sorry, etc.) from code analysis
- **Dashboard generation**: Project-wide statistics and key declarations

## Module Structure

- `SBSBlueprint.Genre`: Genre definition and extension points
- `SBSBlueprint.Hooks`: `\lean{}`, `\uses{}`, and other blueprint hooks
- `SBSBlueprint.Manifest`: Manifest types and serialization
- `SBSBlueprint.Render`: HTML/site generation

## Usage

```lean
import SBSBlueprint

-- Define a blueprint document using Verso syntax
def myBlueprint : Part SBSBlueprint := ...
```

-/

/-!
## Re-exports

The submodules define everything in the `Verso.Genre.SBSBlueprint` namespace.
Users can import `SBSBlueprint` to get access to:

- `Verso.Genre.SBSBlueprint.SBSBlueprint` - The genre definition
- `Verso.Genre.SBSBlueprint.BlueprintMetadata` - Part metadata
- `Verso.Genre.SBSBlueprint.NodeStatus` - Status types
- `Verso.Genre.SBSBlueprint.BlockExt` - Block extensions
- `Verso.Genre.SBSBlueprint.InlineExt` - Inline extensions
- `Verso.Genre.SBSBlueprint.Manifest.*` - Manifest types

Directives (from Hooks.lean):
- `:::leanNode "label"` - Full side-by-side display
- `:::paperStatement "label"` - Statement with signature
- `:::paperFull "label"` - Full side-by-side
- `:::paperProof "label"` - Proof only
- `:::leanModule "ModuleName"` - All module nodes

Roles (from Hooks.lean):
- `{nodeRef "label"}` - Reference link
- `{statusDot "proven"}` - Status indicator
- `{htmlSpan "class"}` - Span wrapper
-/
