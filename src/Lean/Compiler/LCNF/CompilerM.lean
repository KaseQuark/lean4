/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.CoreM
import Lean.Compiler.LCNF.Basic
import Lean.Compiler.LCNF.LCtx

namespace Lean.Compiler.LCNF

/--
The state managed by the `CompilerM` `Monad`.
-/
structure CompilerM.State where
  /--
  A `LocalContext` to store local declarations from let binders
  and other constructs in as we move through `Expr`s.
  -/
  lctx     : LCtx := {}
  /-- Next auxiliary variable suffix -/
  nextIdx : Nat := 1
deriving Inhabited

abbrev CompilerM := StateRefT CompilerM.State CoreM

instance : AddMessageContext CompilerM where
  addMessageContext msgData := do
    let env ← getEnv
    let lctx := (← get).lctx.toLocalContext
    let opts ← getOptions
    return MessageData.withContext { env, lctx, opts, mctx := {} } msgData

def getLocalDecl (fvarId : FVarId) : CompilerM LocalDecl := do
  let some decl := (← get).lctx.localDecls.find? fvarId | throwError "unknown free variable {fvarId.name}"
  return decl

def findFunDecl? (fvarId : FVarId) : CompilerM (Option FunDecl) :=
  return (← get).lctx.funDecls.find? fvarId

def getFunDecl (fvarId : FVarId) : CompilerM FunDecl := do
  let some decl ← findFunDecl? fvarId | throwError "unknown local function {fvarId.name}"
  return decl

@[inline] def modifyLCtx (f : LCtx → LCtx) : CompilerM Unit := do
   modify fun s => { s with lctx := f s.lctx }

def eraseFVar (fvarId : FVarId) : CompilerM Unit := do
  modifyLCtx fun lctx => lctx.erase fvarId

/--
A free variable substitution.
We use these substitutions when inlining definitions and "internalizing" LCNF code into `CompilerM`.
During the internalization process, we ensure all free variables in the LCNF code do not collide with existing ones
at the `CompilerM` local context.
Remark: in LCNF, (computationally relevant) data is in A-normal form, but this is not the case for types and type formers.
So, when inlining we often want to replace a free variable with a type or type former.
-/
abbrev FVarSubst := Std.HashMap FVarId Expr

private partial def normExprImp (s : FVarSubst) (e : Expr) : Expr :=
  go e
where
  go (e : Expr) : Expr :=
    if e.hasFVar then
      match e with
      | .fvar fvarId => s.find? fvarId |>.getD e
      | .lit .. | .const .. | .sort .. | .mvar .. | .bvar .. => e
      | .app f a => e.updateApp! (go f) (go a)
      | .mdata _ b => e.updateMData! (go b)
      | .proj _ _ b => e.updateProj! (go b)
      | .forallE _ d b _ => e.updateForallE! (go d) (go b)
      | .lam _ d b _ => e.updateLambdaE! (go d) (go b)
      | .letE .. => unreachable! -- Valid LCNF does not contain `let`-declarations
    else
      e

private def normFVarImp (s : FVarSubst) (fvarId : FVarId) : FVarId :=
  match s.find? fvarId with
  | some (.fvar fvarId') => fvarId'
  | some _ => panic! "invalid LCNF substitution of free variable with expression"
  | none => fvarId

class MonadFVarSubst (m : Type → Type) where
  getSubst : m FVarSubst
  modifySubst : (FVarSubst → FVarSubst) → m Unit

export MonadFVarSubst (getSubst modifySubst)

@[inline] def addSubst [MonadFVarSubst m] (fvarId : FVarId) (e : Expr) : m Unit :=
  modifySubst fun s => s.insert fvarId e

@[inline] def addFVarSubst [MonadFVarSubst m] (fvarId fvarId' : FVarId) : m Unit :=
  addSubst fvarId (.fvar fvarId')

@[inline] def normFVar [MonadFVarSubst m] [Monad m] (fvarId : FVarId) : m FVarId :=
  return normFVarImp (← getSubst) fvarId

@[inline] def normExpr [MonadFVarSubst m] [Monad m] (e : Expr) : m Expr :=
  return normExprImp (← getSubst) e

def normExprs [MonadFVarSubst m] [Monad m] (es : Array Expr) : m (Array Expr) :=
  es.mapMonoM normExpr

namespace Internalize

abbrev M := StateRefT FVarSubst CompilerM

instance : MonadFVarSubst M where
  getSubst := get
  modifySubst := modify

private def mkNewFVarId (fvarId : FVarId) : M FVarId := do
  let fvarId' ← Lean.mkFreshFVarId
  modify fun s => s.insert fvarId (.fvar fvarId')
  return fvarId'

private def addParam (p : Param) : M Param := do
  let type ← normExpr p.type
  let fvarId ← mkNewFVarId p.fvarId
  modifyLCtx fun lctx => lctx.addLocalDecl fvarId p.binderName type
  return { p with fvarId, type }

mutual

partial def internalizeFunDecl (decl : FunDecl) : M FunDecl := do
  let type ← normExpr decl.type
  let params ← decl.params.mapM addParam
  let value ← internalizeCode decl.value
  let fvarId ← mkNewFVarId decl.fvarId
  let decl := { decl with fvarId, params, type, value }
  modifyLCtx fun lctx => lctx.addFunDecl decl
  return decl

partial def internalizeCode (code : Code) : M Code := do
  match code with
  | .let decl k =>
    let type ← normExpr decl.type
    let value ← normExpr decl.value
    let fvarId ← mkNewFVarId decl.fvarId
    modifyLCtx fun lctx => lctx.addLetDecl fvarId decl.binderName type value
    let k ← internalizeCode k
    return .let { decl with fvarId, type, value } k
  | .fun decl k =>
    return .fun (← internalizeFunDecl decl) (← internalizeCode k)
  | .jp decl k =>
    return .jp (← internalizeFunDecl decl) (← internalizeCode k)
  | .return fvarId => return .return (← normFVar fvarId)
  | .jmp fvarId args => return .jmp (← normFVar fvarId) (← args.mapM normExpr)
  | .unreach type => return .unreach (← normExpr type)
  | .cases c =>
    let discr ← normFVar c.discr
    let alts ← c.alts.mapM fun
      | .alt ctorName params k => return .alt ctorName (← params.mapM addParam) (← internalizeCode k)
      | .default k => return .default (← internalizeCode k)
    return .cases { c with discr, alts }

end

end Internalize

/--
Refresh free variables ids in `code`, and store their declarations in the local context.
-/
partial def Code.internalize (code : Code) (s : FVarSubst := {}) : CompilerM Code :=
  Internalize.internalizeCode code |>.run' s

open Internalize in
def Decl.internalize (decl : Decl) (s : FVarSubst := {}): CompilerM Decl :=
  go decl |>.run' s
where
  go (decl : Decl) : M Decl := do
    let type ← normExpr decl.type
    let params ← decl.params.mapM addParam
    let value ← internalizeCode decl.value
    return { decl with type, params, value }

/-!
Helper functions for creating LCNF local declarations.
-/

def mkParam (binderName : Name) (type : Expr) : CompilerM Param := do
  let fvarId ← mkFreshFVarId
  modifyLCtx fun lctx => lctx.addLocalDecl fvarId binderName type
  return { fvarId, binderName, type }

def mkLetDecl (binderName : Name) (type : Expr) (value : Expr) (pure := true) : CompilerM LetDecl := do
  let fvarId ← mkFreshFVarId
  modifyLCtx fun lctx => lctx.addLetDecl fvarId binderName type value
  return { fvarId, binderName, type, value, pure }

def mkFunDecl (binderName : Name) (type : Expr) (params : Array Param) (value : Code) : CompilerM FunDecl := do
  let fvarId ← mkFreshFVarId
  let funDecl := { fvarId, binderName, type, params, value }
  modifyLCtx fun lctx => lctx.addFunDecl funDecl
  return funDecl

private unsafe def updateParamImp (p : Param) (type : Expr) : CompilerM Param := do
  if ptrEq type p.type then
    return p
  else
    let p := { p with type }
    modifyLCtx fun lctx => lctx.addLocalDecl p.fvarId p.binderName p.type
    return p

@[implementedBy updateParamImp] opaque Param.update (p : Param) (type : Expr) : CompilerM Param

private unsafe def updateLetDeclImp (decl : LetDecl) (type : Expr) (value : Expr) : CompilerM LetDecl := do
  if ptrEq type decl.type && ptrEq value decl.value then
    return decl
  else
    let decl := { decl with type, value }
    modifyLCtx fun lctx => lctx.addLetDecl decl.fvarId decl.binderName decl.type decl.value
    return decl

@[implementedBy updateLetDeclImp] opaque LetDecl.update (decl : LetDecl) (type : Expr) (value : Expr) : CompilerM LetDecl

private unsafe def updateFunDeclImp (decl: FunDecl) (type : Expr) (params : Array Param) (value : Code) : CompilerM FunDecl := do
  if ptrEq type decl.type && ptrEq params decl.params && ptrEq value decl.value then
    return decl
  else
    let decl := { decl with type, params, value }
    modifyLCtx fun lctx => lctx.addFunDecl decl
    return decl

@[implementedBy updateFunDeclImp] opaque FunDeclCore.update (decl: FunDecl) (type : Expr) (params : Array Param) (value : Code) : CompilerM FunDecl

abbrev FunDeclCore.update' (decl : FunDecl) (type : Expr) (value : Code) : CompilerM FunDecl :=
  decl.update type decl.params value

abbrev FunDeclCore.updateValue (decl : FunDecl) (value : Code) : CompilerM FunDecl :=
  decl.update decl.type decl.params value

@[inline] def normParam [MonadLiftT CompilerM m] [Monad m] [MonadFVarSubst m] (p : Param) : m Param := do
  p.update (← normExpr p.type)

def normParams [MonadLiftT CompilerM m] [Monad m] [MonadFVarSubst m] (ps : Array Param) : m (Array Param) :=
  ps.mapMonoM normParam

def normLetDecl [MonadLiftT CompilerM m] [Monad m] [MonadFVarSubst m] (decl : LetDecl) : m LetDecl := do
  decl.update (← normExpr decl.type) (← normExpr decl.value)

def mkFreshBinderName (binderName := `_x): CompilerM Name := do
  let declName := .num binderName (← get).nextIdx
  modify fun s => { s with nextIdx := s.nextIdx + 1 }
  return declName

def mkFreshJpName : CompilerM Name := do
  mkFreshBinderName `_jp

def mkAuxParam (type : Expr) : CompilerM Param := do
  mkParam (← mkFreshBinderName `_y) type

/--
Create a fresh local context and internalize the given decls.
-/
def cleanup (decl : Array Decl) : CompilerM (Array Decl) := do
  modify fun _ => {}
  decl.mapM fun decl => do
    modify fun s => { s with nextIdx := 1 }
    decl.internalize

def CompilerM.run (x : CompilerM α) (s : State := {}) : CoreM α :=
  x |>.run' s

end Lean.Compiler.LCNF
