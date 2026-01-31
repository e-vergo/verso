# Verso (Side-by-Side Blueprint Fork)

This is a fork of [Verso](https://github.com/leanprover/verso), a document authoring framework for Lean developed by David Thrane Christiansen at the Lean FRO. This fork adds genres for mathematical blueprint documents that display formal Lean proofs alongside LaTeX theorem statements.

**Upstream repository:** https://github.com/leanprover/verso

## What This Fork Adds

This fork extends Verso with two new genres for the [Side-by-Side Blueprint](https://github.com/e-vergo/Side-By-Side-Blueprint) toolchain:

1. **SBSBlueprint** - A genre for mathematical formalization blueprints
2. **VersoPaper** (also called **Paper**) - A genre for academic papers with blueprint integration

It also adds **rainbow bracket matching** and **line comment highlighting** to Verso's code rendering system.

All original Verso functionality remains intact.

## Genres

### SBSBlueprint

A document genre for mathematical blueprints that pairs LaTeX theorem statements with Lean formalizations in a side-by-side display. Defined in `src/verso-sbs/SBSBlueprint/Genre.lean`.

**Block directives:**

| Directive | Purpose |
|-----------|---------|
| `:::leanNode "label"` | Full side-by-side display (statement + proof + Lean code) |
| `:::paperStatement "label"` | Statement with Lean signature only |
| `:::paperFull "label"` | Statement + proof + full Lean code |
| `:::paperProof "label"` | Proof body only |
| `:::leanModule "Module.Name"` | All nodes from a module |

**Inline roles:**

| Role | Purpose |
|------|---------|
| `{nodeRef "label"}` | Reference link to a blueprint node |
| `{statusDot "proven"}` | Status indicator dot |
| `{htmlSpan "class"}` | HTML span wrapper |

**Genre definition:**

```lean
def SBSBlueprint : Genre where
  PartMetadata := BlueprintMetadata
  Block := BlockExt
  Inline := InlineExt
  TraverseContext := TraverseContext
  TraverseState := TraverseState
```

The `BlueprintMetadata` structure supports the full set of `@[blueprint]` metadata options: `id`, `title`, `keyDeclaration`, `message`, `priorityItem`, `blocked`, `potentialIssue`, `technicalDebt`, `misc`, and `manualStatus`.

### VersoPaper (Paper)

A genre for academic papers that can reference pre-built blueprint artifacts. Defined in `src/verso-paper/VersoPaper/Basic.lean`.

**Block directives:**

| Directive | Purpose |
|-----------|---------|
| `:::paperStatement "label"` | Insert LaTeX statement with link to Lean code |
| `:::paperFull "label"` | Insert full side-by-side display |
| `:::paperProof "label"` | Insert proof only |
| `:::leanNode "label"` | Insert a Lean node by label |
| `:::leanModule "ModuleName"` | Insert all nodes from a module |
| `:::htmlDiv "classes"` | Wrapper div with custom CSS classes |
| `:::htmlWrapper "tag"` | Wrapper with custom HTML tag and attributes |

**Inline roles:**

| Role | Purpose |
|------|---------|
| `{nodeRef "label"}` | Reference link to a blueprint node |
| `{leanCode}` | Inline Lean code (wrapped in span) |
| `{htmlSpan "classes"}` | Inline span with CSS classes |

**Genre definition:**

```lean
def Paper : Genre where
  PartMetadata := Paper.PartMetadata
  Block := Paper.BlockExt
  Inline := Paper.InlineExt
  TraverseContext := Paper.TraverseContext
  TraverseState := Paper.TraverseState
```

The Paper genre's `PartMetadata` supports `shortTitle`, `number`, `htmlId`, and `showInToc` options for section configuration.

## Node Status Model

Both genres use a 6-status color model for tracking formalization progress:

| Status | Color | Hex | Source |
|--------|-------|-----|--------|
| `notReady` | Sandy Brown | #F4A460 | Default or manual flag |
| `ready` | Light Sea Green | #20B2AA | Manual flag |
| `sorry` | Dark Red | #8B0000 | Auto-detected from proof |
| `proven` | Light Green | #90EE90 | Auto-detected (complete proof) |
| `fullyProven` | Forest Green | #228B22 | Auto-computed (all ancestors proven) |
| `mathlibReady` | Light Blue | #87CEEB | Manual flag |

The `NodeStatus` type in `SBSBlueprint/Genre.lean` provides JSON serialization with backwards compatibility: `"stated"` maps to `.notReady` and `"inMathlib"` maps to `.mathlibReady`.

## Rainbow Bracket Matching

This fork adds rainbow bracket matching to Verso's code highlighting system. The implementation is in `src/verso/Verso/Code/Highlighted.lean`.

**Algorithm:**

The implementation uses a two-pass approach:
1. **Collection pass**: Walks the `Highlighted` AST to find all brackets, recording their positions and IDs
2. **Matching pass**: Uses per-type stacks (`()`, `[]`, `{}`) but a **single global depth counter** shared across all bracket types for visual nesting
3. **Rendering pass**: Generates HTML with color classes based on assigned depths

**Features:**
- Paired bracket matching for `()`, `[]`, and `{}`
- 6-color cycling based on nesting depth (shared across all bracket types)
- Unmatched brackets marked with error color
- Brackets inside string literals (`Token.Kind.str`) and doc comments (`Token.Kind.docComment`) are not colored
- Line comment highlighting (`-- ...` to end of line) via `findCommentRanges`

**API:**

```lean
-- Standard rendering (no rainbow brackets)
hl.toHtml

-- Rainbow bracket rendering
hl.toHtmlRainbow
hl.blockHtmlRainbow contextName code
hl.inlineHtmlRainbow contextName code
```

**CSS classes:**
- `.lean-bracket-1` through `.lean-bracket-6` for matched brackets at different depths
- `.lean-bracket-error` for unmatched brackets
- `.line-comment` for line comments

The CSS includes both light and dark mode variants, embedded in `highlightingStyle`.

**Key types:**

```lean
-- Color assignment
inductive Brackets.BracketColor where
  | matched (depth : Nat)  -- depth mod 6 gives class index
  | error

-- Match state with shared depth
structure Brackets.MatchState where
  parenStack : Array Nat
  bracketStack : Array Nat
  braceStack : Array Nat
  globalDepth : Nat  -- Shared across all bracket types
  colorMap : Std.HashMap Nat Brackets.BracketColor
```

## Package Structure

| Library | Location | Purpose |
|---------|----------|---------|
| `SBSBlueprint` | `src/verso-sbs/` | Blueprint genre |
| `VersoPaper` | `src/verso-paper/` | Paper genre |
| `Verso` | `src/verso/` | Core framework (upstream) |
| `VersoManual` | `src/verso-manual/` | Manual genre (upstream) |
| `VersoBlog` | `src/verso-blog/` | Blog genre (upstream) |

### SBSBlueprint Module Structure

| Module | Purpose |
|--------|---------|
| `SBSBlueprint.Genre` | Genre definition, `NodeStatus`, `BlockExt`, `InlineExt`, `BlueprintMetadata`, traversal instances |
| `SBSBlueprint.Hooks` | Directive and role expanders (`@[directive_expander]`, `@[role_expander]`) |
| `SBSBlueprint.Manifest` | Manifest types and loading |
| `SBSBlueprint.Render` | HTML rendering functions |
| `SBSBlueprint.Main` | Additional utilities |

The Hooks module uses `@[implemented_by]` opaque helpers to avoid `Block.other` name resolution ambiguity at elaboration time.

### VersoPaper Module Structure

| Module | Purpose |
|--------|---------|
| `VersoPaper.Basic` | Genre definition, `BlockExt`, `InlineExt`, `PartMetadata`, `Config`, traversal types |
| `VersoPaper.Blocks` | Block directive and role handlers |
| `VersoPaper.Manifest` | Manifest types (`Node`, `Manifest`) and loading |
| `VersoPaper.Html` | `GenreHtml Paper` instance, CSS, helper rendering functions |

## Usage

### As a Dependency

Add to your `lakefile.lean`:

```lean
require verso from git "https://github.com/e-vergo/verso.git"@"main"
```

Or `lakefile.toml`:

```toml
[[require]]
name = "verso"
git = "https://github.com/e-vergo/verso.git"
rev = "main"
```

### Writing a Blueprint Document

```lean
import SBSBlueprint

open Verso.Genre.SBSBlueprint

#doc (SBSBlueprint) "My Blueprint" =>

# Chapter One

:::leanNode "thm:main"

This displays the main theorem with its Lean formalization.

:::leanModule "MyProject.Lemmas"

This inserts all nodes from the specified module.
```

### Writing a Paper Document

```lean
import VersoPaper

open Verso.Genre.Paper

#doc (Paper) "My Paper" =>

# Introduction

See {nodeRef "thm:main"}`the main theorem` for details.

:::paperStatement "thm:main"

The statement appears here with its Lean signature.

:::paperFull "lem:helper"

Full side-by-side display of statement and proof.
```

### Manifest Integration

Both genres load `manifest.json` (generated by Dress) at render time. The manifest contains:

- Node URLs and metadata
- Status counts
- Validation check results
- Key declarations
- User messages

Pre-rendered artifacts are loaded from `.lake/build/dressed/{Module}/{label}/`:

| File | Content |
|------|---------|
| `decl.html` | Syntax-highlighted Lean code |
| `decl.tex` | LaTeX source |
| `decl.json` | Metadata |
| `decl.hovers.json` | Hover tooltip data |

## Integration with Side-by-Side Blueprint

This fork is part of the larger Side-by-Side Blueprint toolchain:

```
SubVerso -> LeanArchitect -> Dress -> Runway
              |
              +-> Verso (this fork)
```

**Dependency relationships:**
- SubVerso provides syntax highlighting with O(1) indexed lookups via `InfoTable`
- LeanArchitect defines the `@[blueprint]` attribute and `Node` types
- Dress captures artifacts during compilation and generates `manifest.json`
- Runway generates the final site, loading manifest and using Verso for document rendering

**Build flow:**
1. **LeanArchitect** marks declarations with `@[blueprint]` attribute
2. **Dress** captures artifacts during Lean compilation (with `BLUEPRINT_DRESS=1`)
3. **Verso** provides document genres for rendering (SBSBlueprint for blueprints, VersoPaper for papers)
4. **Runway** generates the final site using Verso output and manifest data

## Dependencies

- **Lean:** v4.27.0
- **SubVerso:** Fork at https://github.com/e-vergo/subverso.git (includes O(1) indexed lookups via `InfoTable`)
- **MD4Lean:** Markdown parsing
- **Plausible:** Property-based testing

## Testing

Run tests with:

```bash
lake test
```

Browser tests for JavaScript functionality are in `browser-tests/` and require Playwright.

## License

Verso is licensed under the Apache 2.0 license. See [LICENSE](./LICENSE) for details.

The core Verso framework is copyright Lean FRO LLC. Fork additions are copyright Side-by-Side Blueprint Authors.
