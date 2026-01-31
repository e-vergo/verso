/-
Copyright (c) 2025 Side-by-Side Blueprint Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SBSBlueprint.Genre
import SBSBlueprint.Manifest
import Verso.Doc.Elab.Monad
import Verso.Doc.Elab.Block
import Verso.Doc.ArgParse

/-!
# Blueprint Hook Directives

This module provides Verso directive syntax for inserting blueprint node content
into documents. Hooks resolve at compile-time by referencing labels that will be
looked up in manifest.json during rendering.

## Hook Types

The hook types match the LaTeX semantics from the original blueprint system:

1. `:::leanNode "label"` - Full side-by-side display (statement + proof + Lean code)
2. `:::paperStatement "label"` - Statement with Lean signature only
3. `:::paperFull "label"` - Statement + proof + full Lean code
4. `:::paperProof "label"` - Proof body only
5. `:::leanModule "Module.Name"` - All nodes from a module

## Usage

```
# My Theorem

:::leanNode "thm:main"

This inserts the full side-by-side display for the node labeled "thm:main".

:::paperStatement "lem:helper"

Just the statement and signature, useful in paper contexts.
```

## Implementation Notes

- Hooks create BlockExt values that are rendered by the GenreHtml instance
- The actual content comes from manifest.json and artifact files
- Missing nodes show a warning message rather than failing compilation
- The manifest path defaults to `.lake/build/dressed/manifest.json`
-/

namespace Verso.Genre.SBSBlueprint

open Lean Elab
open Verso Doc Elab
open Verso.ArgParse

/-!
## Block and Inline Constructors

These helper functions work around name ambiguity in quotations.
When directive expanders use `Block.other`, the name is resolved at elaboration
time in user files where both `Lean.Doc.Block.other` and `Verso.Doc.Block.other`
are visible. Both are aliases for the same underlying constructor.

We use `private` implementation functions with `@[implemented_by]` to create
truly opaque helpers that cannot be unfolded during elaboration.
-/

private unsafe def mkLeanNodeBlockUnsafe (label : String) : Block SBSBlueprint :=
  Verso.Doc.Block.other (BlockExt.leanNode label) #[]

@[implemented_by mkLeanNodeBlockUnsafe]
opaque mkLeanNodeBlock (label : String) : Block SBSBlueprint

private def mkPaperStatementBlockImpl (label : String) : Block SBSBlueprint :=
  Verso.Doc.Block.other (BlockExt.paperStatement label) #[]

@[implemented_by mkPaperStatementBlockImpl]
opaque mkPaperStatementBlock (label : String) : Block SBSBlueprint

private def mkPaperFullBlockImpl (label : String) : Block SBSBlueprint :=
  Verso.Doc.Block.other (BlockExt.paperFull label) #[]

@[implemented_by mkPaperFullBlockImpl]
opaque mkPaperFullBlock (label : String) : Block SBSBlueprint

private def mkPaperProofBlockImpl (label : String) : Block SBSBlueprint :=
  Verso.Doc.Block.other (BlockExt.paperProof label) #[]

@[implemented_by mkPaperProofBlockImpl]
opaque mkPaperProofBlock (label : String) : Block SBSBlueprint

private def mkLeanModuleBlockImpl (moduleName : String) : Block SBSBlueprint :=
  Verso.Doc.Block.other (BlockExt.leanModule moduleName) #[]

@[implemented_by mkLeanModuleBlockImpl]
opaque mkLeanModuleBlock (moduleName : String) : Block SBSBlueprint

private def mkNodeRefInlineImpl (label : String) (content : Array (Inline SBSBlueprint)) : Inline SBSBlueprint :=
  Verso.Doc.Inline.other (InlineExt.nodeRef label) content

@[implemented_by mkNodeRefInlineImpl]
opaque mkNodeRefInline (label : String) (content : Array (Inline SBSBlueprint)) : Inline SBSBlueprint

private def mkStatusDotInlineImpl (status : NodeStatus) : Inline SBSBlueprint :=
  Verso.Doc.Inline.other (InlineExt.statusDot status) #[]

@[implemented_by mkStatusDotInlineImpl]
opaque mkStatusDotInline (status : NodeStatus) : Inline SBSBlueprint

private def mkHtmlSpanInlineImpl (classes : String) (content : Array (Inline SBSBlueprint)) : Inline SBSBlueprint :=
  Verso.Doc.Inline.other (InlineExt.htmlSpan classes) content

@[implemented_by mkHtmlSpanInlineImpl]
opaque mkHtmlSpanInline (classes : String) (content : Array (Inline SBSBlueprint)) : Inline SBSBlueprint

/-!
## Block Directive Expanders

These functions expand directive syntax into block expressions containing
the appropriate BlockExt values for hooks.
-/

/--
Insert a full side-by-side display for a blueprint node.

Usage:
```
:::leanNode "thm:main"
```

This displays:
- LaTeX statement paired with Lean signature
- LaTeX proof paired with Lean proof body
- Status indicator dot
- Links between LaTeX and Lean versions
-/
@[directive_expander leanNode]
def leanNode : DirectiveExpander
  | args, _contents => do
    let label ← ArgParse.run (.positional `label .string) args
    -- Use the irreducible helper to avoid Block.other name ambiguity
    return #[← ``(mkLeanNodeBlock $(quote label))]

/--
Insert the LaTeX statement for a blueprint node, with a link to the Lean code.

Usage:
```
:::paperStatement "thm:main"
```

This displays:
- LaTeX statement (theorem/lemma/definition text)
- Lean signature (type declaration)
- Status indicator
- No proof content

Useful for paper contexts where you want to reference the statement
without including the full proof.
-/
@[directive_expander paperStatement]
def paperStatement : DirectiveExpander
  | args, _contents => do
    let label ← ArgParse.run (.positional `label .string) args
    return #[← ``(Verso.Genre.SBSBlueprint.mkPaperStatementBlock $(quote label))]

/--
Insert the full side-by-side display for a blueprint node.

Usage:
```
:::paperFull "thm:main"
```

This is equivalent to `leanNode` and displays:
- LaTeX statement paired with Lean signature
- LaTeX proof paired with Lean proof body
- Status indicator dot

The name `paperFull` matches the LaTeX `\paperfull{}` macro.
-/
@[directive_expander paperFull]
def paperFull : DirectiveExpander
  | args, _contents => do
    let label ← ArgParse.run (.positional `label .string) args
    return #[← ``(Verso.Genre.SBSBlueprint.mkPaperFullBlock $(quote label))]

/--
Insert just the proof for a blueprint node.

Usage:
```
:::paperProof "thm:main"
```

This displays:
- LaTeX proof only
- Lean proof body only
- No statement/signature

Useful when the statement has already been shown elsewhere and you
want to include only the proof.
-/
@[directive_expander paperProof]
def paperProof : DirectiveExpander
  | args, _contents => do
    let label ← ArgParse.run (.positional `label .string) args
    return #[← ``(Verso.Genre.SBSBlueprint.mkPaperProofBlock $(quote label))]

/--
Insert all Lean nodes from a module.

Usage:
```
:::leanModule "MyProject.Theorems"
```

This expands to display all nodes whose `moduleName` matches the given module.
The nodes are rendered in the order they appear in the module.

Useful for automatically including all declarations from a Lean file
without manually listing each label.
-/
@[directive_expander leanModule]
def leanModule : DirectiveExpander
  | args, _contents => do
    let moduleName ← ArgParse.run (.positional `moduleName .string) args
    return #[← ``(Verso.Genre.SBSBlueprint.mkLeanModuleBlock $(quote moduleName))]

/-!
## Inline Role Expanders

These functions expand role syntax into inline expressions for
referencing blueprint nodes within text.
-/

/--
A reference to a blueprint node that creates a hyperlink.

Usage: `{nodeRef "thm:main"}`\`Main Theorem\``

Creates a link to the node. The URL is resolved during the traversal pass
by looking up the label in the node registry.
-/
@[role_expander nodeRef]
def nodeRef : RoleExpander
  | args, content => do
    let label ← ArgParse.run (.positional `label .string <|> pure "") args
    let inlines ← content.mapM elabInline
    return #[← ``(Verso.Genre.SBSBlueprint.mkNodeRefInline $(quote label) #[$inlines,*])]

/--
A status indicator dot showing the node's current status.

Usage: `{statusDot "proven"}`\`\``

Valid status values: notReady, ready, sorry, proven, fullyProven, mathlibReady

The dot is colored according to the 6-status color model.
-/
@[role_expander statusDot]
def statusDot : RoleExpander
  | args, _content => do
    let statusStr ← ArgParse.run (.positional `status .string <|> pure "notReady") args
    -- Construct the appropriate NodeStatus term based on the string
    let statusTerm ← match statusStr with
      | "ready" => ``(NodeStatus.ready)
      | "sorry" => ``(NodeStatus.sorry)
      | "proven" => ``(NodeStatus.proven)
      | "fullyProven" => ``(NodeStatus.fullyProven)
      | "mathlibReady" => ``(NodeStatus.mathlibReady)
      | _ => ``(NodeStatus.notReady)
    return #[← ``(Verso.Genre.SBSBlueprint.mkStatusDotInline $statusTerm)]

/--
An HTML span element with the given classes.

Usage: `{htmlSpan "highlight important"}`\`text\``

Wraps the content in a `<span class="highlight important">` element.
-/
@[role_expander htmlSpan]
def htmlSpan : RoleExpander
  | args, content => do
    let classes ← ArgParse.run (.positional `classes .string <|> pure "") args
    let inlines ← content.mapM elabInline
    return #[← ``(Verso.Genre.SBSBlueprint.mkHtmlSpanInline $(quote classes) #[$inlines,*])]

end Verso.Genre.SBSBlueprint
