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
import Lean.Data.Lsp.Basic

namespace Lean.Widget
open Server

structure NewEnterPath where
  path? : Option (Array Nat)
  deriving ToJson, FromJson

structure MoveCursorAfterZoomPosition where
  position? : Option Lsp.Position
  uri? : Option String
  deriving ToJson, FromJson


/-- Get the top level expression from a `CodeWithInfos`. -/
private def getExprFromCodeWithInfos : CodeWithInfos → Expr
  | TaggedText.tag t _ =>
    match t.info.val.info with
      | Lean.Elab.Info.ofTermInfo i => i.expr
      | _ => panic! "no info"
  | _ => panic! "no tag"

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

    -- we get the correct `enter` command by subtracting the number of `true`s in our list
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
      | Name.str _ s => s
      | _ => panic! "no name found"
    return { expr := b, val? := name, listRest := listParam.tail! }

  | Expr.forallE n _ b _ => do
    let name := match n with
      | Name.str _ s => s
      | _ => panic! "no name found"
    return { expr := b, val? := name, listRest := listParam.tail! }

  | Expr.mdata _ b => do
    match b with
      | Expr.mdata _ _ => return { expr := b, val? := none, listRest := listParam }
      | _ => return { expr := b.appFn!.appArg!, val? := none, listRest := listParam.tail!.tail! }

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
  while !((toString t.cur.getKind) == "Lean.Parser.Tactic.Conv.conv" || (toString t.cur.getKind) == "Lean.Parser.Tactic.Conv.convConvSeq") do
    t := t.up
    pathAfterConv := path.head!::pathAfterConv
    path := path.tail!

  -- the cursor is in front of the first tactic or at the conv atom, we need to do some extra work
  if pathAfterConv == [] || pathAfterConv.length == 1 then
    pathAfterConv := [t.cur.getArgs.size - 2]

  -- the cursor is in front of another tactic, we need to do some extra work
  else if pathAfterConv.length == 3 then
    let mut rangeList' := rangeList.reverse
    let mut ctr := 0
    while rangeList'.head!.stop < pos do
      ctr := ctr + 1
      rangeList' := rangeList'.tail!
    pathAfterConv := List.append pathAfterConv ((ctr-2)::[0])

  return {pathBeforeConv := path.reverse, pathAfterConv := pathAfterConv }

private partial def extractIndentation (input : String) : String := match "  ".isPrefixOf input with
  | true => "  " ++ extractIndentation (input.drop 2)
  | false => ""

private structure InsertReturn where
  stx : Syntax
  newPath : List Nat

private def insertAfterArrow (stx : Syntax) (pathBeforeConvParam : List Nat) (pathAfterConvParam : List Nat) (value : String) : InsertReturn := Id.run do
  let mut t := Syntax.Traverser.fromSyntax stx
  let mut pathBeforeConv := pathBeforeConvParam
  while pathBeforeConv.length > 0 do
    t := t.down pathBeforeConv.head!
    pathBeforeConv := pathBeforeConv.tail!
  let mut pathAfterConv := pathAfterConvParam

--move up to find previous whitespace
  let mut pathBeforeConv' := pathBeforeConvParam.reverse
  let mut returnPath := []
  for _ in [:4] do
    t := t.up
    returnPath := pathBeforeConv'.head!::returnPath
    pathBeforeConv' := pathBeforeConv'.tail!
  t := t.up

  --get previous whitespace
  let argNr := pathBeforeConv'.head! - 1
  let prevArg := reprint! t.cur.getArgs[argNr]!
  let mut previousIndentationLine := (prevArg.splitOn "\n").reverse.head!
  let mut previousIndentation :=  extractIndentation previousIndentationLine

  -- move back down to `conv`
  t := t.down pathBeforeConv'.head!
  while returnPath.length > 0 do
    t := t.down returnPath.head!
    returnPath := returnPath.tail!

  -- we also need the whitespace fron the `=>` node
  let arrow := reprint! t.cur.getArgs[pathAfterConv.head!]!
  let mut arrowIndentationLine := (arrow.splitOn "\n").reverse.head!
  let mut arrowIndentation := extractIndentation arrowIndentationLine

  let mut newNode := Syntax.missing
  --if there is an empty conv body, we need to remove the newlines from the `=>`
  if reprint! t.cur.getArgs[pathAfterConv.head! + 1]! == "" || previousIndentation == arrowIndentation then
    let newArrow := Syntax.atom (SourceInfo.original "".toSubstring 0 "".toSubstring 0) "=>\n"
    t := t.setCur (t.cur.setArgs (List.append (t.cur.getArgs.toList.take pathAfterConv.head!) (newArrow::t.cur.getArgs.toList.drop (pathAfterConv.head! + 1))).toArray)
    newNode := Syntax.atom (SourceInfo.original "".toSubstring 0 "".toSubstring 0) ("  " ++ previousIndentation ++ value ++ "\n" ++ arrowIndentation)
  else
    newNode := Syntax.atom (SourceInfo.original "".toSubstring 0 "".toSubstring 0) (value ++ "\n" ++ arrowIndentation)

  -- move down to args of `conv`
  t := t.down (pathAfterConv.head! + 1)
  t := t.down 0
  t := t.down 0

  -- add new node to Syntax and move to the very top
  let newArgList := newNode::t.cur.getArgs.toList
  t := t.setCur (t.cur.setArgs newArgList.toArray)
  while t.parents.size > 0 do
    t := t.up

  let newPath := pathBeforeConvParam ++ (pathAfterConv.head! + 1)::0::0::[0]

  return { stx := t.cur, newPath := newPath }

private def insertAnywhereElse (stx : Syntax) (pathBeforeConvParam : List Nat) (pathAfterConvParam : List Nat) (value : String) : InsertReturn := Id.run do
  let mut t := Syntax.Traverser.fromSyntax stx
  let mut pathBeforeConv := pathBeforeConvParam
  while pathBeforeConv.length > 0 do
    t := t.down pathBeforeConv.head!
    pathBeforeConv := pathBeforeConv.tail!
  let mut pathAfterConv := pathAfterConvParam

--check if other tactics follow after the `conv` block
  let nothingAfterConv := t.up.cur.getArgs.size - 1 == pathBeforeConvParam.reverse.head!

  -- move down to args of `conv`
  for _ in [:3] do
    t := t.down pathAfterConv.head!
    pathAfterConv := pathAfterConv.tail!

  -- check if it's an enter and if yes merge them
  let argAsString := reprint! t.cur.getArgs[pathAfterConv.head!]!
  let mut newval := value
  let mut entersMerged := false
  if toString t.cur.getArgs[pathAfterConv.head!]!.getKind == "Lean.Parser.Tactic.Conv.«convEnter[__]»" then
    let mut additionalArgs := (argAsString.splitOn "\n").head!
    additionalArgs := (additionalArgs.drop "enter [".length).dropRight 1

    let left := value.take "enter [".length
    let right := value.drop "enter [".length
    newval := left ++ additionalArgs ++ ", " ++ right
    entersMerged := true

  --get whitespace from previous tactic and make new node
  let mut argNr := pathAfterConv.head!
  let mut indentation := ""
  if argNr == 0 then
    -- in this case, we need to grab the whitespace from `=>`
    let mut indentationLine := ((reprint! t.up.up.up.cur).splitOn "\n").tail!.head!
    indentation := extractIndentation indentationLine
  else
    argNr := argNr - 2
    let mut prevArg := reprint! t.cur.getArgs[argNr]!
    let mut split := (prevArg.splitOn "\n")
    -- if there is no `\n`, we take the whitespace from the following node instead
    while split.length == 1 do
      argNr := argNr + 2
      prevArg := reprint! t.cur.getArgs[argNr]!
      split := (prevArg.splitOn "\n")

    let mut indentationLine := split.reverse.head!
    indentation := extractIndentation indentationLine

  -- if we are inserting after the last element of the conv block, we need to add additional indentation in front of our tactic,
  -- and remove some at the end.
  let mut frontIndentation := ""
  if pathAfterConv.head! == t.cur.getArgs.size - 1 then
    let lastArg := reprint! t.cur.getArgs[ t.cur.getArgs.size - 1]!
    let mut lastArgIndentationLine := (lastArg.splitOn "\n").reverse.head!
    let mut lastArgIndentation := extractIndentation lastArgIndentationLine

    let numOfWhitespace := indentation.length - lastArgIndentation.length
    for _ in [:numOfWhitespace] do
      frontIndentation := frontIndentation ++ " "
    indentation := indentation.drop numOfWhitespace

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

  let newNode := match entersMerged with
    | true => Syntax.atom (SourceInfo.original "".toSubstring 0 "".toSubstring 0) (newval ++ "\n" ++ indentation)
    | false => Syntax.atom (SourceInfo.original "".toSubstring 0 "".toSubstring 0) (frontIndentation ++ newval ++ "\n" ++ indentation)
  let newArgList := match entersMerged with
    | true => List.append (argList.take (pathAfterConv.head!) ) (newNode::(argList.drop (pathAfterConv.head! + 1)))
    | false => List.append (argList.take (pathAfterConv.head! + 1) ) (newNode::(argList.drop (pathAfterConv.head! + 1)))
  let newPath := match entersMerged with
    | true => pathBeforeConvParam ++ (pathAfterConvParam.take 4)
    | false => pathBeforeConvParam ++ (pathAfterConvParam.take 3) ++ [(pathAfterConvParam.get! 3) + 2]

  t := t.setCur (t.cur.setArgs newArgList.toArray)
  while t.parents.size > 0 do
    t := t.up

  return { stx := t.cur, newPath := newPath }


private def syntaxInsert (stx : Syntax) (pathBeforeConvParam : List Nat) (pathAfterConvParam : List Nat) (value : String) : InsertReturn := Id.run do
  if value == "" then return { stx := stx, newPath := pathBeforeConvParam ++ pathAfterConvParam }
  -- we are right after conv, we need to do something different here
  if pathAfterConvParam.length == 1 then
    return insertAfterArrow stx pathBeforeConvParam pathAfterConvParam value
  else
    return insertAnywhereElse stx pathBeforeConvParam pathAfterConvParam value

structure InsertEnterReturn where
  newPath : NewEnterPath
  applyParams : Lsp.ApplyWorkspaceEditParams

def insertEnter (subexprParam : SubexprInfo) (goalParam : InteractiveGoal) (stx : Syntax) (p : String.Pos) (doc : Lean.Server.FileWorker.EditableDocument): MetaM InsertEnterReturn := do
  let mut list := (SubExpr.Pos.toArray subexprParam.subexprPos).toList
  let mut expr := (getExprFromCodeWithInfos goalParam.type)
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
  let mut val := reprint! inserted.stx

  --drop newlines and whitespace at the end
  let mut syntaxAsList := val.data.reverse
  while syntaxAsList.head! == '\n' || syntaxAsList.head! == ' ' do
    val := val.dropRight 1
    syntaxAsList := syntaxAsList.tail!

  -- insert new syntax into document
  let text := doc.meta.text

  let textEdit : Lsp.TextEdit := { range := { start := text.utf8PosToLspPos range.start, «end» := text.utf8PosToLspPos { byteIdx := range.stop.byteIdx } }, newText := val }
  let textDocumentEdit : Lsp.TextDocumentEdit := { textDocument := { uri := doc.meta.uri, version? := doc.meta.version }, edits := [textEdit].toArray }
  let edit := Lsp.WorkspaceEdit.ofTextDocumentEdit textDocumentEdit
  let applyParams : Lsp.ApplyWorkspaceEditParams := { label? := "insert `enter` tactic", edit := edit }

  return { newPath := { path? := inserted.newPath.toArray }, applyParams := applyParams }

def findPos (newPathParam : List Nat) (stx : Syntax) : String.Pos := Id.run do
  let mut t := Syntax.Traverser.fromSyntax stx
  let mut newPath := newPathParam
  while !newPath.isEmpty do
    t := t.down newPath.head!
    newPath := newPath.tail!
  let ret := match t.cur.getRange? with
    | some x => x.stop
    | none => panic! "couldn't get position"
  return ret

end Lean.Widget
