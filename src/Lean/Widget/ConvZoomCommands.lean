/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Böhne
-/
import Lean.Widget.InteractiveGoal
import Lean.Meta.ExprLens
import Lean.Server.InfoUtils
import Lean.Server.FileWorker.Utils
import Lean.Data.Lsp.Utf16

namespace Lean.Widget
open Server

structure ConvZoomCommands where
  commands? : Option String
  deriving ToJson, FromJson

/-- Get the top level expression from a `CodeWithInfos`. -/
private partial def getExprFromCodeWithInfos (expression : CodeWithInfos) : List Expr := Id.run do
  let mut list := []
  match expression with
  | TaggedText.text _ => return list
  | TaggedText.append x =>
    for ex in x do
      let list2 := getExprFromCodeWithInfos ex
      list := List.append list list2
    return list
  | TaggedText.tag t _ =>
    match t.info.val.info with
    | Lean.Elab.Info.ofTermInfo i => return List.concat list i.expr
    | _ => return list

private structure SolveReturn where
  expr : Expr
  val? : Option String
  listRest : List Nat

private def solveLevel (expr : Expr) (listParam : List Nat) : MetaM SolveReturn := match expr with
  | Expr.app _ _ => do
    let mut descExp := expr
    let mut count := 0
    let mut explicitList := []

    -- we go through the application until we reach the end, counting how many explicit arguments it has and noting whether
    -- they are explicit or implicit
    while descExp.isApp do
      if (←Lean.Meta.inferType descExp.appFn!).bindingInfo!.isExplicit then
        explicitList := true::explicitList
        count := count + 1
      else
        explicitList := false::explicitList
      descExp := descExp.appFn!

    -- we get the correct `enter` command
    let mut list := listParam
    let mut length := count
    explicitList := List.reverse explicitList
    while !list.isEmpty && list.head! == 0 do
      if explicitList.head! == true then
        count := count - 1
      explicitList := explicitList.tail!
      list := list.tail!

    let mut nextExp := expr
    while length > count do
      nextExp := nextExp.appFn!
      length := length - 1
    nextExp := nextExp.appArg!

    let listRest := if list.isEmpty then [] else list.tail!

    return { expr := nextExp, val? := toString count , listRest := listRest }

  | Expr.lam n _ b _ => do
    let name := match n with
      | Name.anonymous => "anonymus"
      | Name.str _ s => s
      | Name.num _ _ => toString (listParam.head! + 1)
    return { expr := b, val? := name, listRest := listParam.tail! }

  | Expr.forallE n _ b _ => do
    let name := match n with
      | Name.anonymous => "anonymus"
      | Name.str _ s => s
      | Name.num _ _ => toString (listParam.head! + 1)
    return { expr := b, val? := name, listRest := listParam.tail! }

  | Expr.mdata _ b => do
    match b with
      | Expr.mdata _ _ => return {expr := b, val? := none, listRest := listParam }
      | _ => return {expr := b.appFn!.appArg!, val? := none, listRest := listParam.tail!.tail! }

  | _ => do
    return { expr := ←(Lean.Core.viewSubexpr listParam.head! expr), val? := toString ((listParam.head!) + 1), listRest := listParam.tail! }


def reprint! (stx : Syntax) : String :=
  match stx.reprint with
    | some x => x
    | none =>  panic! "Could not reprint syntax"


structure LocateReturn where
  pathBeforeConv : List Nat
  pathAfterConv : List Nat
deriving Inhabited

private def locate (stx : Syntax) (pos : String.Pos) : LocateReturn := Id.run do
  let mut t := Syntax.Traverser.fromSyntax stx
  let mut path := []
  let mut rangeList := []

  -- first, we roughly locate `pos` in the syntax
  while !t.cur.getArgs.isEmpty do
    let mut args := t.cur.getArgs
    let mut i := 0
    let mut newT := t
    let mut found := false
    rangeList := []
    for arg in args do
      let mut range := match arg.getRange? with
        | some x => x
        | none => { start := 0, stop := 0 }
      rangeList := range::rangeList
      if range.start < pos && pos <= range.stop then do
        newT := t.down i
        path := i::path
        found := true
      i := i + 1
    if !found then break
    t := newT

  -- go back up from found location to the first `conv` we find
  let mut pathAfterConv := []
  let mut firstArg := reprint! t.cur
  while !("conv".isPrefixOf firstArg) do
    t := t.up
    firstArg :=reprint! t.cur.getArgs[0]!
    pathAfterConv := path.head!::pathAfterConv
    path := path.tail!

  -- the cursor is in front of the first tactic, we need to do some extra work
  if t.cur.getArgs[0]!.getKind.toString == "Lean.Parser.Tactic.Conv.conv" then
    t := t.down 0
    path := 0::path
    pathAfterConv := [3]

  -- the cursor is in front of another tactic, we need to do some extra work
  else if pathAfterConv.length == 3 then
    let mut rangeList' := rangeList.reverse
    let mut ctr := 0
    while rangeList'.head!.stop < pos do
      ctr := ctr + 1
      rangeList' := rangeList'.tail!
    pathAfterConv := List.append pathAfterConv ((ctr-1)::0::0::[])

  return {pathBeforeConv := path.reverse, pathAfterConv := pathAfterConv }

private def syntaxInsert (stx : Syntax) (pathBeforeConvParam : List Nat) (pathAfterConvParam : List Nat) (value : String) : Syntax := Id.run do
  if value == "" then return stx
  let mut t := Syntax.Traverser.fromSyntax stx
  let mut pathBeforeConv := pathBeforeConvParam
  while pathBeforeConv.length > 0 do
    t := t.down pathBeforeConv.head!
    pathBeforeConv := pathBeforeConv.tail!
  let mut pathAfterConv := pathAfterConvParam

  -- we are right after conv, we need to do something different here
  if pathAfterConv.length == 1 then

    --if there is an empty conv body, we need to remove the newlines from the `=>`
    if reprint! t.cur.getArgs[pathAfterConv.head! + 1]! == "" then
      let newArrow := Syntax.atom (SourceInfo.original "".toSubstring 0 "".toSubstring 0) "=>\n"
      t := t.setCur (t.cur.setArgs (List.append (t.cur.getArgs.toList.take pathAfterConv.head!) (newArrow::t.cur.getArgs.toList.drop (pathAfterConv.head! + 1))).toArray)


    --move up to find previous whitespace
    let mut pathBeforeConv' := pathBeforeConvParam.reverse
    let mut returnPath := []
    for _ in [:4] do
      t := t.up
      returnPath := pathBeforeConv'.head!::returnPath
      pathBeforeConv' := pathBeforeConv'.tail!
    t := t.up

    --get whitespace
    let argNr := pathBeforeConv'.head! - 1
    let prevArg := reprint! t.cur.getArgs[argNr]!
    let mut whitespaceLine := (prevArg.splitOn "\n").reverse.head!
    --whitespace is extended by two spaces to get correct indentation level
    let mut whitespace := "  "
    while "  ".isPrefixOf whitespaceLine do
      whitespace := whitespace ++ "  "
      whitespaceLine := whitespaceLine.drop 2

    -- move back down to `conv`
    t := t.down pathBeforeConv'.head!
    while returnPath.length > 0 do
      t := t.down returnPath.head!
      returnPath := returnPath.tail!

    -- move down to args of `conv`
    t := t.down (pathAfterConv.head! + 1)
    t := t.down 0
    t := t.down 0

    -- if the conv body is empty, we need to add the whitespace in front of the `enter`
    let newNode := match reprint! t.cur.getArgs[0]! with
      | "" => Syntax.atom (SourceInfo.original "".toSubstring 0 "".toSubstring 0) (whitespace ++ value ++ "\n")
      | _ => Syntax.atom (SourceInfo.original "".toSubstring 0 "".toSubstring 0) (value ++ "\n" ++ whitespace)

    -- add new node to Syntax and move to the very top
    let newArgList := newNode::t.cur.getArgs.toList
    t := t.setCur (t.cur.setArgs newArgList.toArray)
    while t.parents.size > 0 do
      t := t.up

    return t.cur

  -- we are anywhere else in the `conv` block
  else
    --check if other tactics follow after the `conv` block
    let nothingAfterConv := t.up.up.cur.getArgs.size - 1 == pathBeforeConvParam.reverse.tail!.head!

    -- move down to args of `conv`
    for _ in [:3] do
      t := t.down pathAfterConv.head!
      pathAfterConv := pathAfterConv.tail!

    -- check if it's an enter and if yes merge them
    let argAsString := reprint! t.cur.getArgs[pathAfterConv.head!]!
    let mut newval := value
    let mut convsMerged := false
    if "enter".isPrefixOf argAsString then
      let mut additionalArgs := (argAsString.splitOn "\n").head!
      additionalArgs := (additionalArgs.drop 7).dropRight 1

      let left := value.take 7
      let right := value.drop 7
      newval := left ++ additionalArgs ++ ", " ++ right
      convsMerged := true

    --get whitespace from previous tactic and make new node
    let mut argNr := pathAfterConv.head!
    if argNr != 0 then argNr := argNr - 1
    let prevArg := reprint! t.cur.getArgs[argNr]!
    let mut whitespaceLine := (prevArg.splitOn "\n").reverse.head!
    let mut whitespace := ""
    while "  ".isPrefixOf whitespaceLine do
      whitespace := whitespace ++ "  "
      whitespaceLine := whitespaceLine.drop 2
    -- if we are inserting after the last element of the conv block, we need to add additional indentation in front of our tactic,
    -- and remove some at the end.
    let mut frontWhitespace := ""
    if pathAfterConv.head! == t.cur.getArgs.size - 1 then
      let mut secondWhitespace := ""
      let lastArg := reprint! t.cur.getArgs[ t.cur.getArgs.size - 1]!
      let mut secondWhitespaceLine := (lastArg.splitOn "\n").reverse.head!
      while "  ".isPrefixOf secondWhitespaceLine do
        secondWhitespace := secondWhitespace ++ "  "
        secondWhitespaceLine := secondWhitespaceLine.drop 2
      let numOfWhitespace := whitespace.length - secondWhitespace.length
      for _ in [:numOfWhitespace] do
        frontWhitespace := frontWhitespace ++ " "
        whitespace := whitespace.drop 1
      -- in this case, we only have one tactic in the conv block, so `numOfWhitespace == 0`, but we still need to add indentation
      if t.cur.getArgs.size == 1 then
        for _ in [:whitespace.length] do
        frontWhitespace := frontWhitespace ++ " "

    let newNode := Syntax.atom (SourceInfo.original "".toSubstring 0 "".toSubstring 0) (frontWhitespace ++ newval ++ "\n" ++ whitespace)
    -- add new node to syntax and move to the very top
    let mut argList := []
    --if there are no tactics after the conv block, we need to remove all but one `\n` from the last tactic
    if nothingAfterConv then
      let mut adjustedLastLine := reprint! t.cur.getArgs[t.cur.getArgs.size - 1]!
      while adjustedLastLine.takeRight 1 == "\n" do
        adjustedLastLine := adjustedLastLine.dropRight 1
      adjustedLastLine := adjustedLastLine ++ "\n"
      let adjustedLastNode := Syntax.atom (SourceInfo.original "".toSubstring 0 "".toSubstring 0) adjustedLastLine
      argList := (adjustedLastNode::t.cur.getArgs.toList.reverse.tail!).reverse
    else
      argList := t.cur.getArgs.toList

    let newArgList := match convsMerged with
      | false => List.append (argList.take (pathAfterConv.head! + 1) ) (newNode::(argList.drop (pathAfterConv.head! + 1)))
      | true => List.append (argList.take (pathAfterConv.head!) ) (newNode::(argList.drop (pathAfterConv.head! + 1)))
    t := t.setCur (t.cur.setArgs newArgList.toArray)
    while t.parents.size > 0 do
      t := t.up

    return t.cur

structure ConvZoomReturn where
  commands : ConvZoomCommands
  applyParams : Lsp.ApplyWorkspaceEditParams

def buildConvZoomCommands (subexprParam : SubexprInfo) (goalParam : InteractiveGoal) (stx : Syntax) (p : String.Pos) (doc : Lean.Server.FileWorker.EditableDocument): MetaM ConvZoomReturn := do
  let mut list := (SubExpr.Pos.toArray subexprParam.subexprPos).toList
  let mut expr := (getExprFromCodeWithInfos goalParam.type).head!
  let mut retList := []
  -- generate list of commands for `enter`
  while !list.isEmpty do
    let res ← solveLevel expr list
    expr := res.expr
    retList := match res.val? with
      | none => retList
      | some val => val::retList
    list := res.listRest

  -- build `enter [...]` string
  retList := List.reverse retList
  let mut enterval := "enter " ++ toString retList
  if enterval.contains '0' then enterval := "Error: Not a valid conv target"
  if retList.isEmpty then enterval := ""

  let mut range := match stx.getRange? with
        | some x => x
        | none => panic! "could not get range"

  -- insert `enter [...]` string into syntax
  let located := (locate stx { byteIdx := (min p.byteIdx range.stop.byteIdx) })
  let inserted := syntaxInsert stx located.pathBeforeConv located.pathAfterConv enterval
  let val := reprint! inserted

  -- insert new syntax into document
  let text := doc.meta.text

  let commands : ConvZoomCommands := { commands? := "" }

  let mut stop := range.stop.byteIdx + 2
  if p.byteIdx == range.stop.byteIdx then stop := p.byteIdx + 1
  if text.source.length == range.stop.byteIdx then stop := text.source.length

  let textEdit : Lsp.TextEdit := { range := { start := text.utf8PosToLspPos range.start, «end» := text.utf8PosToLspPos { byteIdx := stop } }, newText := val }
  let textDocumentEdit : Lsp.TextDocumentEdit := { textDocument := { uri := doc.meta.uri, version? := doc.meta.version }, edits := [textEdit].toArray }
  let edit : Lsp.WorkspaceEdit := { changes? := none, documentChanges? := [textDocumentEdit].toArray , changeAnnotations? := none }
  let applyParams : Lsp.ApplyWorkspaceEditParams := { label? := "insert `enter` tactic", edit := edit }

  return { commands := commands, applyParams := applyParams }

end Lean.Widget
