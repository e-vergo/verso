/-
Copyright (c) 2025 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/
import VersoPaper.Basic
import VersoPaper.Manifest
import Verso.Doc.Html
import Verso.Output.Html

/-!
# HTML Rendering for VersoPaper

This module provides the GenreHtml instance for the Paper genre,
enabling HTML rendering of paper documents with blueprint integration.

The actual node data comes from the manifest which should be loaded
by the caller and made available via the TraverseContext.
-/

namespace Verso.Genre.Paper

open Verso Doc Output Html
open VersoPaper.Manifest (Node Manifest)

/-!
## Helper Functions for HTML Rendering
-/

/--
Render status as a colored dot and text.
-/
def renderStatusBadge (status : String) : Html :=
  let (color, label) := match status with
    | "notReady" => ("#F4A460", "Not Ready")
    | "ready" => ("#20B2AA", "Ready")
    | "sorry" => ("#8B0000", "Sorry")
    | "proven" => ("#90EE90", "Proven")
    | "fullyProven" => ("#228B22", "Fully Proven")
    | "mathlibReady" => ("#87CEEB", "Mathlib Ready")
    | _ => ("#F4A460", status)
  Html.tag "span" #[("class", "status-badge")] <|
    Html.seq #[
      Html.tag "span" #[("class", "status-dot"), ("style", s!"background-color: {color};"), ("title", label)] Html.empty,
      Html.tag "span" #[("class", "status-text")] (.text true label)
    ]

/--
Render a node's statement with Lean signature side-by-side.
-/
def renderStatement (node : Node) : Html :=
  let statusDot := renderStatusBadge node.status
  let title := node.title.getD node.label
  let envType := node.envType.capitalize
  Html.tag "div" #[("class", "paper-statement")] <|
    Html.seq #[
      Html.tag "div" #[("class", "statement-header")] <|
        Html.seq #[
          statusDot,
          Html.tag "span" #[("class", "env-type")] (.text true envType),
          Html.tag "span" #[("class", "statement-title")] (.text true title)
        ],
      Html.tag "div" #[("class", "side-by-side")] <|
        Html.seq #[
          Html.tag "div" #[("class", "latex-side")] <|
            .text false node.statementHtml,
          Html.tag "div" #[("class", "lean-side")] <|
            match node.signatureHtml with
            | some html => .text false html
            | none => Html.tag "em" #[] (.text true "(No Lean signature)")
        ]
    ]

/--
Render a node's proof with Lean proof body side-by-side.
-/
def renderProof (node : Node) : Html :=
  let hasLatexProof := node.proofHtml.isSome && node.proofHtml.getD "" != ""
  let hasLeanProof := node.proofBodyHtml.isSome && node.proofBodyHtml.getD "" != ""

  if !hasLatexProof && !hasLeanProof then
    Html.empty
  else
    Html.tag "div" #[("class", "paper-proof")] <|
      Html.tag "div" #[("class", "side-by-side")] <|
        Html.seq #[
          Html.tag "div" #[("class", "latex-side")] <|
            match node.proofHtml with
            | some html => .text false html
            | none => Html.empty,
          Html.tag "div" #[("class", "lean-side")] <|
            match node.proofBodyHtml with
            | some html => .text false html
            | none => Html.empty
        ]

/--
Render a full node display (statement + proof).
-/
def renderFull (node : Node) : Html :=
  Html.tag "div" #[("class", "paper-node")] <|
    Html.seq #[renderStatement node, renderProof node]

/--
Placeholder for missing nodes.
-/
def renderMissing (label : String) : Html :=
  Html.tag "div" #[("class", "paper-node-missing")] <|
    Html.seq #[
      Html.tag "strong" #[] (.text true "Node not found: "),
      .text true label
    ]

/-!
## GenreHtml Instance

The Paper genre's HTML rendering. This handles the custom block and inline
extensions defined in Basic.lean.

Note: The manifest lookup is a placeholder. In a real implementation,
the manifest would be loaded and stored in TraverseState or passed via
a custom context.
-/

instance [Monad m] : GenreHtml Paper m where
  part partHtml metadata contents := do
    -- For now, just render the part normally
    let headerAttrs : Array (String × String) :=
      match metadata.htmlId with
      | some id => #[("id", id)]
      | none => #[]
    let shortTitle := metadata.shortTitle.getD contents.titleString
    partHtml contents fun level title =>
      mkPartHeader level title (headerAttrs.push ("data-short-title", shortTitle))

  block _goI goB container contents := do
    match container with
    | .paperStatement label =>
      -- For now, render a placeholder - manifest integration will be added in Runway
      pure <| Html.tag "div" #[("class", "paper-statement-placeholder"), ("data-label", label)] <|
        .text true s!"[paperStatement: {label}]"

    | .paperFull label =>
      pure <| Html.tag "div" #[("class", "paper-full-placeholder"), ("data-label", label)] <|
        .text true s!"[paperFull: {label}]"

    | .paperProof label =>
      pure <| Html.tag "div" #[("class", "paper-proof-placeholder"), ("data-label", label)] <|
        .text true s!"[paperProof: {label}]"

    | .leanNode label =>
      pure <| Html.tag "div" #[("class", "lean-node-placeholder"), ("data-label", label)] <|
        .text true s!"[leanNode: {label}]"

    | .leanModule moduleName =>
      pure <| Html.tag "div" #[("class", "lean-module-placeholder"), ("data-module", moduleName)] <|
        .text true s!"[leanModule: {moduleName}]"

    | .htmlDiv classes =>
      let renderedContents ← contents.mapM goB
      pure <| Html.tag "div" #[("class", classes)] (.seq renderedContents)

    | .htmlWrapper t attrs =>
      let renderedContents ← contents.mapM goB
      pure <| Html.tag t attrs (.seq renderedContents)

  inline goI container contents := do
    match container with
    | .nodeRef label =>
      let url := s!"#node-{label.replace ":" "-"}"
      let renderedContents ← contents.mapM goI
      if renderedContents.isEmpty then
        pure <| Html.tag "a" #[("href", url), ("class", "node-ref")] (.text true label)
      else
        pure <| Html.tag "a" #[("href", url), ("class", "node-ref")] (.seq renderedContents)

    | .leanCode code =>
      pure <| Html.tag "code" #[("class", "lean-code")] (.text true code)

    | .htmlSpan classes =>
      let renderedContents ← contents.mapM goI
      pure <| Html.tag "span" #[("class", classes)] (.seq renderedContents)

/-!
## CSS for Paper Rendering

Basic styles for the paper layout. These should be included in the
site's stylesheet or added via `assetsDir` in runway.json.
-/

def paperCss : String := "
/* Paper Genre Styles */
.paper-node {
  margin: 1.5em 0;
  padding: 1em;
  border: 1px solid #ddd;
  border-radius: 8px;
}

.paper-statement {
  margin-bottom: 1em;
}

.statement-header {
  display: flex;
  align-items: center;
  gap: 0.5em;
  margin-bottom: 0.5em;
}

.env-type {
  font-weight: bold;
  text-transform: capitalize;
}

.statement-title {
  color: #333;
}

.side-by-side {
  display: grid;
  grid-template-columns: 1fr 1fr;
  gap: 1em;
}

.latex-side, .lean-side {
  padding: 0.5em;
  background: #f9f9f9;
  border-radius: 4px;
  overflow-x: auto;
}

.latex-side {
  border-left: 3px solid #4a90d9;
}

.lean-side {
  border-left: 3px solid #228B22;
}

.paper-proof {
  margin-top: 1em;
}

.paper-node-missing {
  padding: 1em;
  background: #fff3cd;
  border: 1px solid #ffc107;
  border-radius: 4px;
  color: #856404;
}

.lean-module-empty {
  padding: 1em;
  background: #f8f9fa;
  border-radius: 4px;
  color: #666;
}

/* Status badge */
.status-badge {
  display: inline-flex;
  align-items: center;
  gap: 0.25em;
}

.status-dot {
  width: 10px;
  height: 10px;
  border-radius: 50%;
  display: inline-block;
}

.status-text {
  font-size: 0.8em;
  color: #666;
}

/* Inline elements */
.node-ref {
  color: #4a90d9;
  text-decoration: none;
}

.node-ref:hover {
  text-decoration: underline;
}

.lean-code {
  font-family: 'JetBrains Mono', 'Fira Code', monospace;
  background: #f4f4f4;
  padding: 0.1em 0.3em;
  border-radius: 3px;
}

/* Placeholder styles */
.paper-statement-placeholder,
.paper-full-placeholder,
.paper-proof-placeholder,
.lean-node-placeholder,
.lean-module-placeholder {
  padding: 1em;
  background: #e9ecef;
  border: 1px dashed #6c757d;
  border-radius: 4px;
  color: #495057;
  font-style: italic;
}

/* Responsive layout */
@media (max-width: 768px) {
  .side-by-side {
    grid-template-columns: 1fr;
  }
}
"

end Verso.Genre.Paper
