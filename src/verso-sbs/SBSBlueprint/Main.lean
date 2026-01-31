/-
Copyright (c) 2025 Side-by-Side Blueprint Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SBSBlueprint.Genre
import SBSBlueprint.Manifest
import SBSBlueprint.Render

import Verso.Doc
import Verso.Doc.Html
import Verso.Output.Html
import Verso.FS

/-!
# Entry Point for SBSBlueprint Site Generation

This module provides `sbsBlueprintMain`, the main entry point for generating
HTML output from Verso documents using the SBSBlueprint genre.

## Usage

Consumer projects create a main function that calls `sbsBlueprintMain`:

```lean
import SBSBlueprint
import MyBlueprint  -- Module defining the document

open Verso.Genre.SBSBlueprint

def main : IO UInt32 :=
  sbsBlueprintMain (%doc MyBlueprint.blueprint) (config := {
    outputDir := "_out",
    buildDir := ".lake/build",
    -- manifestPath, title, etc.
  })
```

## Configuration

The `Config` structure provides configuration options:
- `outputDir`: Where to write HTML output
- `buildDir`: Where .lake/build is located (for artifacts)
- `manifestPath`: Optional override for manifest.json location
- `title`: Document title
- `baseUrl`: Base URL for links

## Output

Currently generates single-page HTML output. The output includes:
- The main document content
- Side-by-side displays for `leanNode` hooks
- Status indicators from the manifest
- Basic CSS styling

Multi-page output and additional features can be added as needed.
-/

namespace Verso.Genre.SBSBlueprint.Main

open Lean (Json ToJson FromJson)
open Verso Doc Output Html
open Verso.Doc.Html
open Verso.Genre.SBSBlueprint
open Verso.Genre.SBSBlueprint.Manifest
open Verso.Genre.SBSBlueprint.Render

/-!
## Configuration
-/

/--
Configuration for the SBSBlueprint site generator.
-/
structure Config where
  /-- Directory for output files -/
  outputDir : System.FilePath := "_out"
  /-- Path to .lake/build directory (for artifacts) -/
  buildDir : System.FilePath := ".lake/build"
  /-- Override manifest.json location (default: buildDir/dressed/manifest.json) -/
  manifestPath : Option System.FilePath := none
  /-- Document title (used in HTML head) -/
  title : String := "Blueprint"
  /-- Base URL for links (e.g., "/" or "/project/") -/
  baseUrl : String := "/"
  /-- Whether to emit single-page HTML -/
  emitHtmlSingle : Bool := true
  /-- Output filename (without extension) -/
  outputFileName : String := "index"
  /-- Additional CSS files to include -/
  extraCss : Array String := #[]
  /-- Additional JS files to include -/
  extraJs : Array String := #[]
  /-- Whether to be verbose -/
  verbose : Bool := false
  deriving Repr, Inhabited

/--
Default configuration.
-/
def defaultConfig : Config := {}

/-!
## Helper Functions
-/

/--
Ensure a directory exists, creating it if necessary.
-/
def ensureDir (dir : System.FilePath) : IO Unit := do
  if !(← dir.pathExists) then
    IO.FS.createDirAll dir

/--
Get the manifest path from config.
-/
def Config.getManifestPath (cfg : Config) : System.FilePath :=
  cfg.manifestPath.getD (cfg.buildDir / "dressed" / "manifest.json")

/--
Get the artifact directory path.
-/
def Config.getArtifactDir (cfg : Config) : System.FilePath :=
  cfg.buildDir / "dressed"

/-!
## CSS Styles
-/

/--
Default CSS styles for the blueprint.
-/
def defaultStyles : String :=
"
/* Basic reset and typography */
body {
  font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
  line-height: 1.6;
  max-width: 1200px;
  margin: 0 auto;
  padding: 2rem;
  color: #333;
}

/* Side-by-side container */
.sbs-container {
  display: flex;
  gap: 2rem;
  margin: 1rem 0;
  border: 1px solid #e0e0e0;
  border-radius: 4px;
  padding: 1rem;
}

.sbs-latex-column, .sbs-lean-column {
  flex: 1;
  min-width: 0;
}

.sbs-latex-column {
  border-right: 1px solid #e0e0e0;
  padding-right: 1rem;
}

/* Theorem environments */
.theorem_thmwrapper, .lemma_thmwrapper, .definition_thmwrapper,
.proposition_thmwrapper, .corollary_thmwrapper {
  margin: 1rem 0;
}

.theorem_thmheading, .lemma_thmheading, .definition_thmheading,
.proposition_thmheading, .corollary_thmheading {
  font-weight: bold;
  margin-bottom: 0.5rem;
}

.theorem_thmcaption, .lemma_thmcaption, .definition_thmcaption,
.proposition_thmcaption, .corollary_thmcaption {
  font-style: italic;
  margin-right: 0.5rem;
}

/* Status dots */
.status-dot {
  display: inline-block;
  width: 8px;
  height: 8px;
  border-radius: 50%;
  margin-left: 0.5rem;
}

.header-status-dot {
  width: 10px;
  height: 10px;
}

/* Lean code */
.lean-code {
  background-color: #f8f8f8;
  padding: 1rem;
  border-radius: 4px;
  overflow-x: auto;
  font-family: 'Fira Code', 'Monaco', monospace;
  font-size: 0.9rem;
}

/* Proof toggle */
.proof_wrapper {
  margin-top: 1rem;
  padding-top: 0.5rem;
  border-top: 1px solid #e0e0e0;
}

.proof_caption {
  font-style: italic;
}

.expand-proof {
  color: #0066cc;
  cursor: pointer;
  margin-left: 0.5rem;
}

/* Missing node warning */
.sbs-missing-node {
  background-color: #fff3cd;
  border: 1px solid #ffc107;
  padding: 1rem;
  border-radius: 4px;
  margin: 1rem 0;
}

.sbs-missing-node .warning {
  color: #856404;
  margin: 0;
}

/* Paper mode */
.paper-theorem {
  margin: 1rem 0;
  padding: 1rem;
  border-left: 4px solid #0066cc;
  background-color: #f8f9fa;
}

.paper-theorem-header {
  display: flex;
  align-items: center;
  gap: 0.5rem;
  margin-bottom: 0.5rem;
}

.paper-theorem-type {
  font-weight: bold;
}

.blueprint-link {
  font-size: 0.8rem;
  color: #0066cc;
}
"

/-!
## HTML Generation
-/

/--
Generate the HTML head element.
-/
def generateHead (cfg : Config) (pageTitle : String) : Html :=
  let cssLinks := cfg.extraCss.map fun css =>
    .tag "link" #[("rel", "stylesheet"), ("href", css)] Html.empty
  let jsScripts := cfg.extraJs.map fun js =>
    .tag "script" #[("src", js)] (.text true "")

  .tag "head" #[] (.seq #[
    .tag "meta" #[("charset", "utf-8")] Html.empty,
    .tag "meta" #[("name", "viewport"), ("content", "width=device-width, initial-scale=1")] Html.empty,
    .tag "title" #[] (.text true pageTitle),
    -- Default styles
    .tag "style" #[] (.text true defaultStyles),
    -- Extra CSS
    .seq cssLinks,
    -- Extra JS
    .seq jsScripts
  ])

/-!
## Rendering Functions

These are partial functions that handle the recursive structure of documents.
-/

/--
Render an inline element to HTML.
-/
partial def renderInline (ctx : RenderContext) (inline : Doc.Inline SBSBlueprint) : IO Html := do
  match inline with
  | .text str => pure (.text true str)
  | .linebreak _ => pure (.tag "br" #[] Html.empty)
  | .emph contents =>
    let inlineHtmls ← contents.toList.mapM (renderInline ctx)
    pure (.tag "em" #[] (.seq inlineHtmls.toArray))
  | .bold contents =>
    let inlineHtmls ← contents.toList.mapM (renderInline ctx)
    pure (.tag "strong" #[] (.seq inlineHtmls.toArray))
  | .code str => pure (.tag "code" #[] (.text true str))
  | .link contents dest =>
    let inlineHtmls ← contents.toList.mapM (renderInline ctx)
    pure (.tag "a" #[("href", dest)] (.seq inlineHtmls.toArray))
  | .image alt dest =>
    pure (.tag "img" #[("src", dest), ("alt", alt)] Html.empty)
  | .concat inlines =>
    let inlineHtmls ← inlines.toList.mapM (renderInline ctx)
    pure (.seq inlineHtmls.toArray)
  | .other ext contents =>
    let inlineHtmls ← contents.toList.mapM (renderInline ctx)
    let contentHtml := Html.seq inlineHtmls.toArray
    Render.renderInlineExt ctx ext contentHtml
  | .math _mode content =>
    -- Simple math rendering - could use KaTeX
    pure (.tag "span" #[("class", "math")] (.text true content))
  | .footnote id contents =>
    let inlineHtmls ← contents.toList.mapM (renderInline ctx)
    pure (.tag "span" #[("class", "footnote"), ("id", s!"fn-{id}")] (.seq inlineHtmls.toArray))

/--
Render a block to HTML.
-/
partial def renderBlock (ctx : RenderContext) (block : Doc.Block SBSBlueprint) : IO Html := do
  match block with
  | .para contents =>
    let inlineHtmls ← contents.toList.mapM (renderInline ctx)
    pure (.tag "p" #[] (.seq inlineHtmls.toArray))
  | .concat blocks =>
    let blockHtmls ← blocks.toList.mapM (renderBlock ctx)
    pure (.seq blockHtmls.toArray)
  | .other ext contents =>
    -- Use the render functions from Render.lean
    let contentBlocks ← contents.toList.mapM (renderBlock ctx)
    let extHtml ← Render.renderBlockExt ctx ext
    if extHtml == Html.empty then
      -- Extension didn't render, use default
      pure (.tag "div" #[] (.seq contentBlocks.toArray))
    else
      pure extHtml
  | .blockquote contents =>
    let blockHtmls ← contents.toList.mapM (renderBlock ctx)
    pure (.tag "blockquote" #[] (.seq blockHtmls.toArray))
  | .ul items =>
    let itemHtmls ← items.toList.mapM fun item => do
      let blockHtmls ← item.contents.toList.mapM (renderBlock ctx)
      pure (.tag "li" #[] (.seq blockHtmls.toArray))
    pure (.tag "ul" #[] (.seq itemHtmls.toArray))
  | .ol start items =>
    let itemHtmls ← items.toList.mapM fun item => do
      let blockHtmls ← item.contents.toList.mapM (renderBlock ctx)
      pure (.tag "li" #[] (.seq blockHtmls.toArray))
    let attrs := if start == 1 then #[] else #[("start", toString start)]
    pure (.tag "ol" attrs (.seq itemHtmls.toArray))
  | .dl items =>
    let itemHtmls ← items.toList.mapM fun item => do
      let termHtmls ← item.term.toList.mapM (renderInline ctx)
      let defHtmls ← item.desc.toList.mapM (renderBlock ctx)
      pure (.seq #[
        .tag "dt" #[] (.seq termHtmls.toArray),
        .tag "dd" #[] (.seq defHtmls.toArray)
      ])
    pure (.tag "dl" #[] (.seq itemHtmls.toArray))
  | .code content =>
    pure (.tag "pre" #[] (.tag "code" #[] (.text true content)))

/--
Render a document part to HTML.
-/
partial def renderPart (ctx : RenderContext) (part : Part SBSBlueprint)
    (level : Nat := 1) : IO Html := do
  -- Render title
  let titleHtml := Html.seq (part.title.map fun inline =>
    -- Simple inline rendering - could be enhanced
    match inline with
    | .text str => .text true str
    | _ => .text true ""  -- Placeholder for other inlines
  )

  let headingTag := s!"h{min level 6}"
  let heading := .tag headingTag #[] titleHtml

  -- Render content blocks
  let mut contentHtml : Array Html := #[]
  for block in part.content do
    let blockHtml ← renderBlock ctx block
    contentHtml := contentHtml.push blockHtml

  -- Render subparts
  let mut subPartsHtml : Array Html := #[]
  for sub in part.subParts do
    let subHtml ← renderPart ctx sub (level + 1)
    subPartsHtml := subPartsHtml.push subHtml

  -- Combine
  let sectionId := part.metadata.bind (·.htmlId) |>.getD ""
  let sectionAttrs := if sectionId.isEmpty then #[] else #[("id", sectionId)]

  pure (.tag "section" sectionAttrs (.seq #[
    heading,
    .seq contentHtml,
    .seq subPartsHtml
  ]))

/--
Generate the full HTML page.
-/
def generatePage (cfg : Config) (manifest : Option BlueprintManifest)
    (text : Part SBSBlueprint) : IO Html := do
  let ctx : RenderContext := {
    manifest
    baseUrl := cfg.baseUrl
    artifactDir := cfg.getArtifactDir
    paperMode := false
  }

  let pageTitle := text.metadata.bind (·.title) |>.getD cfg.title
  let head := generateHead cfg pageTitle
  let body ← renderPart ctx text

  pure (.tag "html" #[("lang", "en")] (.seq #[
    head,
    .tag "body" #[] body
  ]))

/-!
## Command-Line Option Parsing
-/

/--
Parse command-line options.
-/
def parseOptions (cfg : Config) : List String → IO Config
  | ("--output" :: dir :: rest) =>
    parseOptions { cfg with outputDir := dir } rest
  | ("--build-dir" :: dir :: rest) =>
    parseOptions { cfg with buildDir := dir } rest
  | ("--manifest" :: path :: rest) =>
    parseOptions { cfg with manifestPath := some path } rest
  | ("--title" :: configTitle :: rest) =>
    parseOptions { cfg with title := configTitle } rest
  | ("--base-url" :: url :: rest) =>
    parseOptions { cfg with baseUrl := url } rest
  | ("--verbose" :: rest) =>
    parseOptions { cfg with verbose := true } rest
  | ("--no-html-single" :: rest) =>
    parseOptions { cfg with emitHtmlSingle := false } rest
  | (unknown :: _) =>
    throw (IO.userError s!"Unknown option: {unknown}")
  | [] => pure cfg

/-!
## Main Entry Point
-/

/--
Main entry point for generating HTML from a Verso SBSBlueprint document.

This function:
1. Loads the manifest.json from the build directory
2. Generates HTML output
3. Writes the output to disk

Example usage:
```lean
def main : IO UInt32 :=
  sbsBlueprintMain (%doc MyBlueprint.document) (config := {
    outputDir := "_out",
    buildDir := ".lake/build",
  })
```
-/
def sbsBlueprintMain (text : Part SBSBlueprint)
    (options : List String := [])
    (config : Config := {}) : IO UInt32 := do
  let cfg ← parseOptions config options

  -- Set up error logging
  let errorCount : IO.Ref Nat ← IO.mkRef 0
  let logError (msg : String) := do
    errorCount.modify (· + 1)
    IO.eprintln s!"Error: {msg}"

  if cfg.verbose then
    IO.println s!"SBSBlueprint: Generating output to {cfg.outputDir}"

  -- Load manifest
  let manifestPath := cfg.getManifestPath
  let manifest ← if ← manifestPath.pathExists then
    if cfg.verbose then
      IO.println s!"  Loading manifest from {manifestPath}"
    match ← loadManifestFrom manifestPath with
    | some m => pure (some m)
    | none =>
      logError s!"Failed to load manifest from {manifestPath}"
      pure none
  else
    if cfg.verbose then
      IO.println s!"  No manifest found at {manifestPath}"
    pure none

  -- Generate HTML
  if cfg.verbose then
    IO.println "  Generating HTML..."

  if cfg.emitHtmlSingle then
    let html ← generatePage cfg manifest text
    let htmlStr := Html.doctype ++ "\n" ++ Html.asString html

    -- Write output
    ensureDir cfg.outputDir
    let outPath := cfg.outputDir / (cfg.outputFileName ++ ".html")
    if cfg.verbose then
      IO.println s!"  Writing {outPath}"
    IO.FS.writeFile outPath htmlStr

  -- Check for errors
  match ← errorCount.get with
  | 0 =>
    if cfg.verbose then
      IO.println "  Done!"
    return 0
  | 1 =>
    IO.eprintln "1 error was encountered."
    return 1
  | n =>
    IO.eprintln s!"{n} errors were encountered."
    return 1

end Verso.Genre.SBSBlueprint.Main

/-!
## Re-export

Re-export `sbsBlueprintMain` at the package level for convenience.
-/

namespace Verso.Genre.SBSBlueprint

open Verso.Genre.SBSBlueprint.Main

/--
Main entry point for SBSBlueprint site generation.

See `Verso.Genre.SBSBlueprint.Main.sbsBlueprintMain` for full documentation.
-/
def sbsBlueprintMain := Main.sbsBlueprintMain

/--
Configuration for SBSBlueprint site generation.
-/
abbrev BlueprintConfig := Main.Config

end Verso.Genre.SBSBlueprint
