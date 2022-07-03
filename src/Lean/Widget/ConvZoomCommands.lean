/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Böhne
-/
import Lean.Widget.InteractiveGoal
import Lean.Meta.ExprLens

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

private def solveLevel (expr : Expr) (listParam : List Nat) : MetaM (SolveReturn) := match expr with
  | Expr.app _ _ _ => do
    let mut descExp := expr
    let mut count := 0
    let mut explicitList := []

    while descExp.isApp do
      if (←Lean.Meta.inferType descExp.appFn!).bindingInfo!.isExplicit then
        explicitList := true::explicitList
        count := count + 1
      else
        explicitList := false::explicitList
      descExp := descExp.appFn!

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

partial def infoToString: SourceInfo → String
  | SourceInfo.original s _ s2 _    => s2.toString
  | SourceInfo.synthetic _ _  => ""
  | _ => ""

partial def stxToString (stx : Syntax) : String := match stx with
  | Syntax.missing => "missing"
  | Syntax.node info kind args => Id.run do
    let mut ret := ""
    for s in args do
      let str := stxToString s
      ret := ret ++ str ++ " "
    if ret != "" && ret != " " && ret != "\n" then ret := ret ++ "\n"
    return ret
  | Syntax.atom _ s => s
  | Syntax.ident _ _ s _=> s.toString

structure Range where
  start : String.Pos
  stop : String.Pos

def getRange? (stx : Syntax) (originalOnly := false) : Option Range :=
  match stx.getPos? originalOnly, stx.getTailPos? originalOnly with
  | some start, some stop => some { start, stop }
  | _,          _         => none

structure LocateReturn where
  path : List Nat
  traverser : Syntax.Traverser
  range : Range
  rangeList : List Range
def mkRange : Range := { start := 0, stop := 0 }

def locate (tParam : Syntax.Traverser) (pos : String.Pos) : LocateReturn := Id.run do
  let mut t := tParam
  let mut path := []
  let mut finrange := mkRange
  while !t.cur.getArgs.isEmpty do
    let mut args := t.cur.getArgs
    let mut i := 0
    let mut newT := t
    let mut found := false
    let mut rangeList := []
    for arg in args do
      let mut range := match getRange? arg with
        | some x => x
        | none => { start := 0, stop := 0 }
      rangeList := range::rangeList
      if range.start < pos && pos <= range.stop then do
        newT := t.down i
        path := i::path
        finrange := range
        found := true
      i := i + 1
    if !found then return { path := path.reverse , traverser := t, range := finrange, rangeList := rangeList }
    t := newT
  return { path := path.reverse , traverser := t, range := finrange, rangeList := []}

structure InsertReturn where
  stx : Syntax
  list : List Syntax
deriving Inhabited

partial def syntaxInsert (stxParam : Syntax) (val : String) (path : List Nat) : InsertReturn := Id.run do
  let mut stx := stxParam
  let pos := path.head!
  if path.tail!.isEmpty then
    match stx with
      | Syntax.missing => panic! "error: missing"
      | Syntax.atom _ _ => panic! "error: atom"
      | Syntax.ident _ _ _ _=> panic! "error: ident"
      | Syntax.node info kind args =>
        let newval := Syntax.atom SourceInfo.none val
        --let lineBreak := Syntax.atom SourceInfo.none ""
        let newArgList := List.append (args.toList.take (pos + 1)) (newval::(args.toList.drop (pos + 1)))
        return { stx := Syntax.node info kind newArgList.toArray, list := newArgList }
  else
    match stx with
      | Syntax.missing => panic! "error: missing"
      | Syntax.atom _ _ => panic! "error: atom"
      | Syntax.ident _ _ _ _=> panic! "error: ident"
      | Syntax.node info kind args =>
        let nextStx := args[pos]!
        let newStx := syntaxInsert nextStx val path.tail!
        let newArgs := args.set! pos newStx.stx
        return { stx := Syntax.node info kind newArgs, list := newStx.list }



def buildConvZoomCommands (subexprParam : SubexprInfo) (goalParam : InteractiveGoal) (stx : Syntax) (p: String.Pos) : MetaM (ConvZoomCommands) := do
  let mut list := (SubExpr.Pos.toArray subexprParam.subexprPos).toList
  let mut expr := (getExprFromCodeWithInfos goalParam.type).head!
  let mut ret := ""
  let mut retList := []
  while !list.isEmpty do

    let res ← solveLevel expr list
    expr := res.expr
    retList := match res.val? with
      | none => retList
      | some val => val::retList
    list := res.listRest

  retList := List.reverse retList
  let mut enterval := "enter " ++ toString retList
  if enterval.contains '0' then enterval := "Error: Not a valid conv target"
  if retList.isEmpty then enterval := ""

  --ret := Format.pretty (←Lean.PrettyPrinter.ppCommand stx)
  --ret := "/-\n" ++ fileMap.source ++ "\n-/"

  let range := match getRange? stx with
  | some x => x
  | none => { start := 0, stop := 0}

  --ret := "start: " ++ toString range.start ++ "stop: " ++ toString range.stop ++ "p: " ++ toString p ++ "\n"
  let traverser := Syntax.Traverser.fromSyntax stx
  let retval := (locate traverser p)
  --ret := ret ++ "path : " ++ retval.path.toString ++ "\n"
  --ret := ret ++ "/-\n" ++ stxToString stx ++ "\n-/"
  let inserted := syntaxInsert stx enterval retval.path
  --ret := ret ++ "\n--------------------------------------------\n"
 -- ret := ret ++ "/-\n" ++ stxToString inserted ++ "\n-/"
  --ret := ret ++ "/-\n" ++ Format.pretty (←Lean.PrettyPrinter.ppCommand inserted.stx) ++ "\n-/"
  let val := match Syntax.reprint inserted.stx with
    | some x => x
    | none => "nichts"
  --ret := ret ++ "/-\n" ++ val ++ "\n-/"
  --ret := ret ++ "/-\n" ++ stxToString retval.traverser.cur ++ "\n-/"
  --ret := ret ++ "/-\n" ++ "start: " ++ toString retval.range.start ++ "stop: " ++ toString retval.range.stop ++ "p: " ++ toString p ++ "\n"
  --for range in retval.rangeList do
    --ret := ret ++ "\n" ++ "start: " ++ toString range.start ++ "stop: " ++ toString range.stop
  ret := "--Result after inserting enter:\n"
  --ret := ret ++ "/-\n" ++ Format.pretty (←Lean.PrettyPrinter.ppCommand inserted.stx) ++ "\n-/"
  ret := ret ++ "/-\n" ++ val ++ "\n-/"
  for stx in inserted.list do
    ret := ret ++ "\n--------------------------------------------\n"
    ret := ret ++ stxToString stx
  ret := ret ++ "\n--------------------------------------------\n"
  /-let last := inserted.list.reverse.head!
  match last with
    | Syntax.missing => panic! "error: missing"
    | Syntax.atom _ _ => panic! "error: atom"
    | Syntax.ident _ _ _ _=> panic! "error: ident"
    | Syntax.node info kind args =>
      ret := ret ++ "\n" ++ toString kind-/

  /-let convtest := retval.testargs.toList.head!
  ret := ret ++ "\n" ++ "convtest: " ++ Format.pretty (←Lean.PrettyPrinter.ppCommand convtest)
  let convtestargs := convtest.getArgs.toList.head!.getArgs
  for arg in convtestargs do
    ret := ret ++ "\n" ++ "testargs: " ++ stxToString arg
  ret := ret ++ "\n" ++ toString convtest.getArgs.size
  let testval := match convtest with
    | Syntax.missing => Array.empty
    | Syntax.node _ _ args => args
    | Syntax.atom _ _ => Array.empty
    | Syntax.ident _ _ _ _=> Array.empty
  let testval2 := match convtest with
    | Syntax.missing => "1"
    | Syntax.node _ _ _ => "2"
    | Syntax.atom _ _ => "3"
    | Syntax.ident _ _ _ _=> "4"
  ret := ret ++ "testval2 :" ++ toString testval2-/
  return { commands? := ret }

end Lean.Widget
