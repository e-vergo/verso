/-
Copyright (c) 2025 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/
import VersoPaper.Basic
import Verso.Doc.Elab.Monad
import Verso.Doc.Elab.Block
import Verso.Doc.ArgParse

/-!
# Paper Block Directives

This module contains the directive and role definitions for paper blocks.
These directives allow inserting blueprint content into Verso documents.

## Directives

- `:::paperStatement "label"` - Insert LaTeX statement with link to Lean
- `:::paperFull "label"` - Insert full side-by-side display
- `:::paperProof "label"` - Insert just the proof
- `:::leanNode "label"` - Insert a Lean node from manifest
- `:::leanModule "ModuleName"` - Insert all nodes from a module
- `:::htmlDiv "classes"` - Wrapper div with custom classes
- `:::htmlWrapper "tag"` - Wrapper with custom HTML tag

## Roles

- `{nodeRef}`\`label\`` - Reference to a blueprint node
- `{leanCode}`\`code\`` - Inline Lean code with highlighting
- `{htmlSpan "classes"}`\`text\`` - Inline span with classes

## Implementation Notes

The actual node content comes from manifest.json which is loaded at runtime.
These directives create block extension values that are rendered by the
GenreHtml Paper instance in Html.lean.
-/

namespace Verso.Genre.Paper

open Lean Elab
open Verso Doc Elab
open Verso.ArgParse

/-!
## Block Directive Expanders

These functions expand directive syntax into block expressions containing
the appropriate BlockExt values.
-/

/--
Insert the LaTeX statement for a blueprint node, with a link to the Lean code.

Usage:
```
:::paperStatement "thm:main"
```

The node's statementHtml and signatureHtml will be rendered side-by-side.
-/
@[directive_expander paperStatement]
def paperStatement : DirectiveExpander
  | args, _contents => do
    let label ← ArgParse.run (.positional `label .string) args
    return #[← ``(Block.other (BlockExt.paperStatement $(quote label)) #[])]

/--
Insert the full side-by-side display for a blueprint node.

Usage:
```
:::paperFull "thm:main"
```

This includes both statement/signature and proof/proofBody in side-by-side layout.
-/
@[directive_expander paperFull]
def paperFull : DirectiveExpander
  | args, _contents => do
    let label ← ArgParse.run (.positional `label .string) args
    return #[← ``(Block.other (BlockExt.paperFull $(quote label)) #[])]

/--
Insert just the proof for a blueprint node.

Usage:
```
:::paperProof "thm:main"
```

Shows the LaTeX proof and Lean proof body without the statement.
-/
@[directive_expander paperProof]
def paperProof : DirectiveExpander
  | args, _contents => do
    let label ← ArgParse.run (.positional `label .string) args
    return #[← ``(Block.other (BlockExt.paperProof $(quote label)) #[])]

/--
Insert a Lean node by label from the manifest.

Usage:
```
:::leanNode "thm:main"
```

This is equivalent to paperFull for most purposes.
-/
@[directive_expander leanNode]
def leanNode : DirectiveExpander
  | args, _contents => do
    let label ← ArgParse.run (.positional `label .string) args
    return #[← ``(Block.other (BlockExt.leanNode $(quote label)) #[])]

/--
Insert all Lean nodes from a module.

Usage:
```
:::leanModule "MyProject.Theorems"
```

Expands to all nodes whose moduleName matches the given module.
-/
@[directive_expander leanModule]
def leanModule : DirectiveExpander
  | args, _contents => do
    let moduleName ← ArgParse.run (.positional `moduleName .string) args
    return #[← ``(Block.other (BlockExt.leanModule $(quote moduleName)) #[])]

/--
A wrapper div with custom CSS classes.

Usage:
```
:::htmlDiv "my-class another-class" {
  Content here
}
```
-/
@[directive_expander htmlDiv]
def htmlDiv : DirectiveExpander
  | args, contents => do
    let classes ← ArgParse.run (.positional `classes .string) args
    let blocks ← contents.mapM elabBlock
    return #[← ``(Block.other (BlockExt.htmlDiv $(quote classes)) #[$blocks,*])]

/--
A wrapper with a custom HTML tag.

Usage:
```
:::htmlWrapper "aside" {
  Content here
}
```
-/
@[directive_expander htmlWrapper]
def htmlWrapper : DirectiveExpander
  | args, contents => do
    let tag ← ArgParse.run (.positional `tag .string) args
    let blocks ← contents.mapM elabBlock
    -- Empty attributes array for now
    return #[← ``(Block.other (BlockExt.htmlWrapper $(quote tag) #[]) #[$blocks,*])]

/-!
## Inline Role Expanders

These functions expand role syntax into inline expressions containing
the appropriate InlineExt values.
-/

/--
A reference to a blueprint node that creates a hyperlink.

Usage: `{nodeRef "thm:main"}`\`link text\``
-/
@[role_expander nodeRef]
def nodeRef : RoleExpander
  | args, content => do
    let label ← ArgParse.run (.positional `label .string <|> pure "") args
    -- If no positional arg provided, use the label as provided or empty
    let inlines ← content.mapM elabInline
    return #[← ``(Inline.other (InlineExt.nodeRef $(quote label)) #[$inlines,*])]

/--
Inline Lean code with highlighting.

Usage: `{leanCode}`\`Nat.add\``

Note: For VersoPaper, this just wraps the code in a span.
Full highlighting requires SubVerso integration.
-/
@[role_expander leanCode]
def leanCode : RoleExpander
  | _args, content => do
    let inlines ← content.mapM elabInline
    return #[← ``(Inline.other (InlineExt.leanCode "") #[$inlines,*])]

/--
An HTML span element with the given classes.

Usage: `{htmlSpan "highlight"}`\`text\``
-/
@[role_expander htmlSpan]
def htmlSpan : RoleExpander
  | args, content => do
    let classes ← ArgParse.run (.positional `classes .string <|> pure "") args
    let inlines ← content.mapM elabInline
    return #[← ``(Inline.other (InlineExt.htmlSpan $(quote classes)) #[$inlines,*])]

end Verso.Genre.Paper
