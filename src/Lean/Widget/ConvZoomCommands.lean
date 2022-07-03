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
  | (Expr.app _ _ _) => do
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

  | (Expr.lam n _ b _) => do
    let name := match n with
      | Name.anonymous => "anonymus"
      | Name.str _ s _ => s
      | Name.num _ _ _ => toString (listParam.head! + 1)
    return { expr := b, val? := name, listRest := listParam.tail! }

  | (Expr.forallE n _ b _) => do
    let name := match n with
      | Name.anonymous => "anonymus"
      | Name.str _ s _ => s
      | Name.num _ _ _ => toString (listParam.head! + 1)
    return { expr := b, val? := name, listRest := listParam.tail! }

  | (Expr.mdata _ b _) => do
    return {expr := b.appFn!.appArg!, val? := none, listRest := listParam.tail!.tail! }

  | _ =>
    let retexpr := match (viewCoordRaw listParam.head! expr) with
      | Except.error _ => expr
      | Except.ok e => e
    return { expr := retexpr, val? := toString ((listParam.head!) + 1), listRest := listParam.tail! }

def buildConvZoomCommands (subexprParam : SubexprInfo) (goalParam : InteractiveGoal) : MetaM (ConvZoomCommands) := do
  let mut ret := "/-\n"
  let mut list := (SubExpr.Pos.toArray subexprParam.subexprPos).toList
  let mut expr := (getExprFromCodeWithInfos goalParam.type).head!
  let mut retList := []
  while !list.isEmpty do

    let res ← solveLevel expr list
    expr := res.expr
    retList := match res.val? with
      | none => retList
      | some val => val::retList
    list := res.listRest

  retList := List.reverse retList
  ret := "enter " ++ toString retList
  if ret.contains '0' then ret := "Error: Not a valid conv target"
  if retList.isEmpty then ret := ""

  return { commands? := ret }

end Lean.Widget
