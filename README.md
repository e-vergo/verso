# Verso (Side-by-Side Blueprint Fork)

This is a fork of [Verso](https://github.com/leanprover/verso), a document authoring framework for Lean developed by David Thrane Christiansen at the Lean FRO. This fork adds genres for mathematical blueprint documents that display formal Lean proofs alongside LaTeX theorem statements.

**Upstream repository:** https://github.com/leanprover/verso

## What This Fork Adds

This fork extends Verso with two new genres for the [Side-by-Side Blueprint](https://github.com/e-vergo/Side-By-Side-Blueprint) toolchain:

1. **SBSBlueprint** - A genre for mathematical formalization blueprints
2. **VersoPaper** - A genre for academic papers with blueprint integration

It also adds **rainbow bracket matching** to Verso's code highlighting system.

All original Verso functionality remains intact.

## Genres

### SBSBlueprint

A document genre for mathematical blueprints that pairs LaTeX theorem statements with Lean formalizations in a side-by-side display.

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

### VersoPaper

A genre for academic papers that can reference pre-built blueprint artifacts.

**Block directives:**

| Directive | Purpose |
|-----------|---------|
| `:::paperStatement "label"` | Insert LaTeX statement with link to Lean code |
| `:::paperFull "label"` | Insert full side-by-side display |
| `:::paperProof "label"` | Insert proof only |
| `:::leanNode "label"` | Insert a Lean node by label |
| `:::leanModule "ModuleName"` | Insert all nodes from a module |
| `:::htmlDiv "classes"` | Wrapper div with custom CSS classes |
| `:::htmlWrapper "tag"` | Wrapper with custom HTML tag |

**Inline roles:**

| Role | Purpose |
|------|---------|
| `{nodeRef "label"}` | Reference link to a blueprint node |
| `{lean "code"}` | Inline Lean code |
| `{span "classes"}` | Inline span with CSS classes |

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

## Rainbow Bracket Matching

This fork adds rainbow bracket matching to Verso's code highlighting system. The implementation is in `src/verso/Verso/Code/Highlighted.lean`.

**Features:**
- Paired bracket matching for `()`, `[]`, and `{}`
- 6-color cycling based on nesting depth (shared across all bracket types)
- Unmatched brackets marked with error color
- Brackets inside string literals and comments are not colored
- Line comment highlighting (`-- ...` to end of line)

**Usage:**

```lean
-- Standard rendering (no rainbow brackets)
hl.toHtml

-- Rainbow bracket rendering
hl.toHtmlRainbow
hl.blockHtmlRainbow contextName code
hl.inlineHtmlRainbow contextName code
```

**CSS classes:** `.lean-bracket-1` through `.lean-bracket-6` for matched brackets, `.lean-bracket-error` for unmatched.

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
| `SBSBlueprint.Genre` | Genre definition, types, traversal instances |
| `SBSBlueprint.Hooks` | Directive and role expanders |
| `SBSBlueprint.Manifest` | Manifest types and loading |
| `SBSBlueprint.Render` | HTML rendering functions |
| `SBSBlueprint.Main` | Additional utilities |

### VersoPaper Module Structure

| Module | Purpose |
|--------|---------|
| `VersoPaper.Basic` | Genre definition and types |
| `VersoPaper.Blocks` | Block directive handlers |
| `VersoPaper.Manifest` | Manifest types and loading |
| `VersoPaper.Html` | HTML rendering functions |

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

## Dependencies

- **Lean:** v4.27.0
- **SubVerso:** Fork at https://github.com/e-vergo/subverso.git (includes O(1) indexed lookups)
- **MD4Lean:** Markdown parsing
- **Plausible:** Property-based testing

## Integration with Side-by-Side Blueprint

This fork is part of the larger Side-by-Side Blueprint toolchain:

```
SubVerso -> LeanArchitect -> Dress -> Runway
              |
              +-> Verso (this fork)
```

The typical build flow:

1. **LeanArchitect** defines `@[blueprint]` attribute for marking declarations
2. **Dress** captures artifacts during Lean compilation
3. **Verso** provides document genres for rendering
4. **Runway** generates the final site using Verso output

## Testing

Run tests with:

```bash
lake test
```

Browser tests for JavaScript functionality are in `browser-tests/` and require Playwright.

## License

Verso is licensed under the Apache 2.0 license. See [LICENSE](./LICENSE) for details.

The core Verso framework is copyright Lean FRO LLC. Fork additions are copyright Side-by-Side Blueprint Authors.
