/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Böhne
-/
import Lean.Widget.InteractiveGoal
import Lean.Meta.ExprLens
import Lean.Server.InfoUtils

namespace Lean.Widget
open Server

open Except in
/-- Get the raw subexpression withotu performing any instantiation. -/
private def viewCoordRaw: Nat → Expr → Except String Expr
  | 3, e                        => error s!"Can't viewRaw the type of {e}"
  | 0, (Expr.app f _ _)       => ok f
  | 1, (Expr.app _ a _)       => ok a
  | 0, (Expr.lam _ y _ _)     => ok y
  | 1, (Expr.lam _ _ b _)     => ok b
  | 0, (Expr.forallE _ y _ _) => ok y
  | 1, (Expr.forallE _ _ b _) => ok b
  | 0, (Expr.letE _ y _ _ _)  => ok y
  | 1, (Expr.letE _ _ a _ _)  => ok a
  | 2, (Expr.letE _ _ _ b _)  => ok b
  | 0, (Expr.proj _ _ b _)    => ok b
  | n, (Expr.mdata _ a _)     => viewCoordRaw n a
  | c, e                        => error s!"Bad coordinate {c} for {e}"

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
  | Expr.app _ _ _ => do
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
      | Name.str _ s _ => s
      | Name.num _ _ _ => toString (listParam.head! + 1)
    return { expr := b, val? := name, listRest := listParam.tail! }

  | Expr.forallE n _ b _ => do
    let name := match n with
      | Name.anonymous => "anonymus"
      | Name.str _ s _ => s
      | Name.num _ _ _ => toString (listParam.head! + 1)
    return { expr := b, val? := name, listRest := listParam.tail! }

  | Expr.mdata _ b _ => do
    match b with
      | Expr.mdata _ _ _ => return {expr := b, val? := none, listRest := listParam }
      | _ => return {expr := b.appFn!.appArg!, val? := none, listRest := listParam.tail!.tail! }

  | _ =>
    let retexpr := match (viewCoordRaw listParam.head! expr) with
      | Except.error _ => expr
      | Except.ok e => e
    return { expr := retexpr, val? := toString ((listParam.head!) + 1), listRest := listParam.tail! }


def reprint! (stx : Syntax) : String :=
  match stx.reprint with
    | some x => x
    | none =>  panic! "Could not reprint syntax"


structure LocateReturn where
  pathBeforeConv : List Nat
  pathAfterConv : List Nat
deriving Inhabited

private def locate (tParam : Syntax.Traverser) (pos : String.Pos) : LocateReturn := Id.run do
  let mut t := tParam
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
  t := t.up
  let mut pathAfterConv := []
  let mut firstArg := reprint! t.cur.getArgs[0]!
  pathAfterConv := path.head!::pathAfterConv
  path := path.tail!
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
  let mut t := Syntax.Traverser.fromSyntax stx
  let mut pathBeforeConv := pathBeforeConvParam
  while pathBeforeConv.length > 0 do
    t := t.down pathBeforeConv.head!
    pathBeforeConv := pathBeforeConv.tail!
  let mut pathAfterConv := pathAfterConvParam

  -- we are right after conv, we need to do something different here
  if pathAfterConv.length == 1 then
    --move up to find previous whitespace
    let mut pathBeforeConv' := pathBeforeConvParam.reverse
    let mut returnPath := []
    for _ in [:4] do
      t := t.up
      returnPath := pathBeforeConv'.head!::returnPath
      pathBeforeConv' := pathBeforeConv'.tail!
    t := t.up

    --get whitespace and make new node
    let argNr := pathBeforeConv'.head! - 1
    let prevArg := reprint! t.cur.getArgs[argNr]!
    let mut whitespaceLine := (prevArg.splitOn "\n").reverse.head!
    --whitespace is extended by two spaces to get correct indentation level
    let mut whitespace := "  "
    while "  ".isPrefixOf whitespaceLine do
      whitespace := whitespace ++ "  "
      whitespaceLine := whitespaceLine.drop 2
    let newNode := Syntax.atom (SourceInfo.original "".toSubstring 0 "".toSubstring 0) (value ++ "\n" ++ whitespace)

    -- move back down to `conv`
    t := t.down pathBeforeConv'.head!
    while returnPath.length > 0 do
      t := t.down returnPath.head!
      returnPath := returnPath.tail!

    -- move down to args of `conv`
    t := t.down (pathAfterConv.head! + 1)
    t := t.down 0
    t := t.down 0

    -- add new node to Syntax and move to the very top
    let newArgList := newNode::t.cur.getArgs.toList
    t := t.setCur (t.cur.setArgs newArgList.toArray)
    while t.parents.size > 0 do
      t := t.up

    return t.cur

  -- we are anywhere else in the `conv` block
  else
     -- move down to args of `conv`
    for _ in [:3] do
      t := t.down pathAfterConv.head!
      pathAfterConv := pathAfterConv.tail!

    --get whitespace from previous tactic and make new node
    let argNr := match pathAfterConv.head! with
      | 0 => 0
      | x => x - 1
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



    let newNode := Syntax.atom (SourceInfo.original "".toSubstring 0 "".toSubstring 0) (frontWhitespace ++ value ++ "\n" ++ whitespace)
    -- add new node to syntax and move to the very top
    let argList := t.cur.getArgs.toList
    let newArgList := List.append (argList.take (pathAfterConv.head! + 1) ) (newNode::(argList.drop (pathAfterConv.head! + 1)))
    t := t.setCur (t.cur.setArgs newArgList.toArray)
    while t.parents.size > 0 do
      t := t.up

    return t.cur

def buildConvZoomCommands (subexprParam : SubexprInfo) (goalParam : InteractiveGoal) (stx : Syntax) (p: String.Pos) (text: FileMap): MetaM ConvZoomCommands := do
  let mut list := (SubExpr.Pos.toArray subexprParam.subexprPos).toList
  let mut expr := (getExprFromCodeWithInfos goalParam.type).head!
  let mut ret := ""
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

  -- insert `enter [...]` string into syntax
  let traverser := Syntax.Traverser.fromSyntax stx
  let retval := (locate traverser p)
  let inserted := syntaxInsert stx retval.pathBeforeConv retval.pathAfterConv enterval
  let val := reprint! inserted

  let mut range := match stx.getRange? with
        | some x => x
        | none => panic! "could not get range"

  -- insert new syntax into document
  let part1 := text.source.take range.start.byteIdx
  let part2 := text.source.drop (range.stop.byteIdx + 2)
  let newsrc := part1 ++ val ++ part2

  ret := ret ++ "--Result after inserting enter:\n"
  ret := ret ++ "/-\n" ++ newsrc ++ "\n-/"

  return { commands? := ret }

end Lean.Widget
