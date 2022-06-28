/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Böhne
-/
import Lean.Widget.InteractiveGoal

namespace Lean.Widget
open Server

open Except in
/-- Get the raw subexpression withotu performing any instantiation. -/
private def viewCoordRaw: Nat → Expr → Except String Expr
  | 3, e                        => error s!"Can't viewRaw the type of {e}"
  | 0, e@(Expr.app f a _)       => ok f
  | 1, e@(Expr.app f a _)       => ok a
  | 0, e@(Expr.lam n y b _)     => ok y
  | 1, e@(Expr.lam n y b c)     => ok b
  | 0, e@(Expr.forallE n y b _) => ok y
  | 1, e@(Expr.forallE n y b c) => ok b
  | 0, e@(Expr.letE n y a b c)  => ok y
  | 1, e@(Expr.letE n y a b c)  => ok a
  | 2, e@(Expr.letE n y a b c)  => ok b
  | 0, e@(Expr.proj _ _ b _)    => ok b
  | n, e@(Expr.mdata _ a _)     => viewCoordRaw n a
  | c, e                        => error s!"Bad coordinate {c} for {e}"

/-- Decodes a subexpression `Pos` as a sequence of coordinates. See `Pos.encode` for details.-/
private def decode (p : Nat) : Array Nat :=
  Lean.SubExpr.Pos.foldl Array.push #[] p

structure ConvZoomCommands where
  commands? : Option String
  deriving RpcEncoding

/-- Get the top level expression from a `CodeWithInfos`. -/
private partial def getExprFromCodeWithInfos (expression : CodeWithInfos) : List Expr := Id.run do
  let mut list := []
  match expression with
  | TaggedText.text t => return list
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
  test : String
  deriving Inhabited

private def solveLevel (expr : Expr) (listParam : List Nat) : MetaM (SolveReturn) := match expr with
| e@(Expr.app _ _ _) => do
  let mut descExp := e
  let mut count := 0
  let mut explicitList := []
  let mut exprList := []

  while descExp.isApp do
    if (←Lean.Meta.inferType descExp.appFn!).bindingInfo!.isExplicit then
      explicitList := true::explicitList
      count := count + 1
    else
      explicitList := false::explicitList
    exprList := descExp::exprList
    descExp := descExp.appFn!

  let mut list := listParam
  let mut length := count
  explicitList := List.reverse explicitList
  while !list.isEmpty && list.head! == 0 do
    if explicitList.head! == true then
      count := count - 1
    explicitList := explicitList.tail!
    list := list.tail!

  let mut nextExp := e
  while length > count do
    nextExp := nextExp.appFn!
    length := length - 1
  nextExp := nextExp.appArg!

  let listRest := if list.isEmpty then [] else list.tail!

  let mut testval := "exp: " ++ Expr.dbgToString expr ++"\nnextExp: " ++ Expr.dbgToString nextExp ++ "\nlistParam: " ++ listParam.toString ++
    "\ncount: " ++ toString count ++ "\nlistRest: " ++ listRest.toString ++ "\nlength: " ++ toString length ++ "\nexplicitList: " ++ explicitList.toString ++"\n"

  for expr in exprList do
    testval := testval ++ "exprFromList: " ++ Expr.dbgToString expr ++ "\n"

  return { expr := nextExp, val? := toString count , listRest := listRest, test := testval }

| e@(Expr.lam n _ b _) => do
  let name := match n with
    | Name.anonymous => "anonymus"
    | Name.str _ s _ => s
    | Name.num _ s _ => toString (listParam.head! + 1)
  return { expr := b, val? := name, listRest := listParam.tail! , test := "lam\n" }

| e@(Expr.forallE n _ b _) => do
  let name := match n with
    | Name.anonymous => "anonymus"
    | Name.str _ s _ => s
    | Name.num _ s _ => toString (listParam.head! + 1)
  return { expr := b, val? := name, listRest := listParam.tail! , test := "forallE\n" }

| e@(Expr.mdata _ b _) => do
  return {expr := b.appFn!.appArg!, val? := none, listRest := listParam.tail!.tail!, test := "mdata\n"}

| e =>
  let retexpr := match (viewCoordRaw listParam.head! expr) with
    | Except.error e => expr
    | Except.ok e => e
  return { expr := retexpr, val? := toString ((listParam.head!) + 1), listRest := listParam.tail! , test := "generic\n" }

def buildConvZoomCommands (subexprParam : SubexprInfo) (goalParam : InteractiveGoal) : MetaM (ConvZoomCommands) := do
let mut ret := "/-\n"
let mut list := (decode subexprParam.subexprPos).toList
let mut expr := (getExprFromCodeWithInfos goalParam.type).head!
let mut retList := []
while !list.isEmpty do

  ret := ret ++ "expr: " ++ Expr.dbgToString expr ++"\n"

  let res ← solveLevel expr list
  expr := res.expr
  retList := match res.val? with
    | none => retList
    | some val => val::retList
  list := res.listRest

  ret := ret ++ "listRest " ++ toString list ++"\n" ++ "\n" ++ res.test ++ "\n\n"

retList := List.reverse retList
ret := ret ++ "-/\n"
ret := "enter " ++ toString retList
if ret.contains '0' then ret := "Error: Not a valid conv target"
if retList.isEmpty then ret := ""

return { commands? := ret }

end Lean.Widget
