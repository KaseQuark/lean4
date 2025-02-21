/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.App
import Lean.Elab.BuiltinNotation

/-! # Auxiliary elaboration functions: AKA custom elaborators -/

namespace Lean.Elab.Term
open Meta

private def getMonadForIn (expectedType? : Option Expr) : TermElabM Expr := do
    match expectedType? with
    | none => throwError "invalid 'for_in%' notation, expected type is not available"
    | some expectedType =>
      match (← isTypeApp? expectedType) with
      | some (m, _) => return m
      | none => throwError "invalid 'for_in%' notation, expected type is not of of the form `M α`{indentExpr expectedType}"

private def throwForInFailure (forInInstance : Expr) : TermElabM Expr :=
  throwError "failed to synthesize instance for 'for_in%' notation{indentExpr forInInstance}"

@[builtinTermElab forInMacro] def elabForIn : TermElab :=  fun stx expectedType? => do
  match stx with
  | `(for_in% $col $init $body) =>
      match (← isLocalIdent? col) with
      | none   => elabTerm (← `(let col := $col; for_in% col $init $body)) expectedType?
      | some colFVar =>
        tryPostponeIfNoneOrMVar expectedType?
        let m ← getMonadForIn expectedType?
        let colType ← inferType colFVar
        let elemType ← mkFreshExprMVar (mkSort (mkLevelSucc (← mkFreshLevelMVar)))
        let forInInstance ← try
          mkAppM ``ForIn #[m, colType, elemType]
        catch _ =>
          tryPostpone; throwError "failed to construct 'ForIn' instance for collection{indentExpr colType}\nand monad{indentExpr m}"
        match (← trySynthInstance forInInstance) with
        | .some inst =>
          let forInFn ← mkConst ``forIn
          elabAppArgs forInFn
            (namedArgs := #[{ name := `m, val := Arg.expr m}, { name := `α, val := Arg.expr elemType }, { name := `self, val := Arg.expr inst }])
            (args := #[Arg.stx col, Arg.stx init, Arg.stx body])
            (expectedType? := expectedType?)
            (explicit := false) (ellipsis := false) (resultIsOutParamSupport := false)
        | .undef    => tryPostpone; throwForInFailure forInInstance
        | .none     => throwForInFailure forInInstance
  | _ => throwUnsupportedSyntax

@[builtinTermElab forInMacro'] def elabForIn' : TermElab :=  fun stx expectedType? => do
  match stx with
  | `(for_in'% $col $init $body) =>
      match (← isLocalIdent? col) with
      | none   => elabTerm (← `(let col := $col; for_in'% col $init $body)) expectedType?
      | some colFVar =>
        tryPostponeIfNoneOrMVar expectedType?
        let m ← getMonadForIn expectedType?
        let colType ← inferType colFVar
        let elemType ← mkFreshExprMVar (mkSort (mkLevelSucc (← mkFreshLevelMVar)))
        let forInInstance ←
          try
            let memType ← mkFreshExprMVar (← mkAppM ``Membership #[elemType, colType])
            mkAppM ``ForIn' #[m, colType, elemType, memType]
          catch _ =>
            tryPostpone; throwError "failed to construct `ForIn'` instance for collection{indentExpr colType}\nand monad{indentExpr m}"
        match (← trySynthInstance forInInstance) with
        | .some inst  =>
          let forInFn ← mkConst ``forIn'
          elabAppArgs forInFn
            (namedArgs := #[{ name := `m, val := Arg.expr m}, { name := `α, val := Arg.expr elemType}, { name := `self, val := Arg.expr inst }])
            (args := #[Arg.expr colFVar, Arg.stx init, Arg.stx body])
            (expectedType? := expectedType?)
            (explicit := false) (ellipsis := false) (resultIsOutParamSupport := false)
        | .undef    => tryPostpone; throwForInFailure forInInstance
        | .none     => throwForInFailure forInInstance
  | _ => throwUnsupportedSyntax

namespace BinOp
/-!

The elaborator for `binop%` terms works as follows:

1- Expand macros.
2- Convert `Syntax` object corresponding to the `binop%` term into a `Tree`.
   The `toTree` method visits nested `binop%` terms and parentheses.
3- Synthesize pending metavariables without applying default instances and using the
   `(mayPostpone := true)`.
4- Tries to compute a maximal type for the tree computed at step 2.
   We say a type α is smaller than type β if there is a (nondependent) coercion from α to β.
   We are currently ignoring the case we may have cycles in the coercion graph.
   If there are "uncomparable" types α and β in the tree, we skip the next step.
   We say two types are "uncomparable" if there isn't a coercion between them.
   Note that two types may be "uncomparable" because some typing information may still be missing.
5- We traverse the tree and inject coercions to the "maximal" type when needed.

Recall that the coercions are expanded eagerly by the elaborator.

Properties:

a) Given `n : Nat` and `i : Nat`, it can successfully elaborate `n + i` and `i + n`. Recall that Lean 3
   fails on the former.

b) The coercions are inserted in the "leaves" like in Lean 3.

c) There are no coercions "hidden" inside instances, and we can elaborate
```
axiom Int.add_comm (i j : Int) : i + j = j + i

example (n : Nat) (i : Int) : n + i = i + n := by
  rw [Int.add_comm]
```
Recall that the `rw` tactic used to fail because our old `binop%` elaborator would hide
coercions inside of a `HAdd` instance.

Remarks:

In the new `binop%` elaborator the decision whether a coercion will be inserted or not
is made at `binop%` elaboration time. This was not the case in the old elaborator.
For example, an instance, such as `HAdd Int ?m ?n`, could be created when executing
the `binop%` elaborator, and only resolved much later. We try to minimize this problem
by synthesizing pending metavariables at step 3.

For types containing heterogeneous operators (e.g., matrix multiplication), step 4 will fail
and we will skip coercion insertion. For example, `x : Matrix Real 5 4` and `y : Matrix Real 4 8`,
there is no coercion `Matrix Real 5 4` from `Matrix Real 4 8` and vice-versa, but
`x * y` is elaborated successfully and has type `Matrix Real 5 8`.
-/

private inductive Tree where
  /--
  Leaf of the tree.
  We store the `infoTrees` generated when elaborating `val`. These trees become
  subtrees of the infotree nodes generated for `op` nodes.
  -/
  | term (ref : Syntax) (infoTrees : PersistentArray InfoTree) (val : Expr)
  /--
  `ref` is the original syntax that expanded into `binop%`.
  `macroName` is the `macro_rule` that produce the expansion. We store this information
  here to make sure "go to definition" behaves similarly to notation defined without using `binop%` helper elaborator.
  -/
  | op (ref : Syntax) (macroName : Name) (lazy : Bool) (f : Expr) (lhs rhs : Tree)

private partial def toTree (s : Syntax) : TermElabM Tree := do
  /-
  Remark: ew used to use `expandMacros` here, but this is a bad idiom
  because we do not record the macro expansion information in the info tree.
  We now manually expand the notation in the `go` function, and save
  the macro declaration names in the `op` nodes.
  -/
  let result ← go s
  synthesizeSyntheticMVars (mayPostpone := true)
  return result
where
  go (s : Syntax) := do
    match s with
    | `(binop% $f $lhs $rhs) => processOp (lazy := false) s .anonymous f lhs rhs
    | `(binop_lazy% $f $lhs $rhs) => processOp (lazy := true) s .anonymous f lhs rhs
    | `(($e)) =>
      if hasCDot e then
        processLeaf s
      else
        go e
    | _ =>
       match (← liftMacroM <| expandMacroImpl? (← getEnv) s) with
       | some (macroName, s?) =>
         let s' ← liftMacroM <| liftExcept s?
         match s' with
         | `(binop% $f $lhs $rhs) => processOp (lazy := false) s macroName f lhs rhs
         | `(binop_lazy% $f $lhs $rhs) => processOp (lazy := true) s macroName f lhs rhs
         | _  => processLeaf s
       | none => processLeaf s

  processOp (ref : Syntax) (declName : Name) (f lhs rhs : Syntax) (lazy : Bool) := do
    let some f ← resolveId? f | throwUnknownConstant f.getId
    return .op (lazy := lazy) ref declName f (← go lhs) (← go rhs)

  processLeaf (s : Syntax) := do
    let e ← elabTerm s none
    let info ← getResetInfoTrees
    return .term s info e

-- Auxiliary function used at `analyze`
private def hasCoe (fromType toType : Expr) : TermElabM Bool := do
  if (← getEnv).contains ``CoeHTCT then
    let u ← getLevel fromType
    let v ← getLevel toType
    let coeInstType := mkAppN (Lean.mkConst ``CoeHTCT [u, v]) #[fromType, toType]
    match ← trySynthInstance coeInstType (some (maxCoeSize.get (← getOptions))) with
    | .some _ => return true
    | .none   => return false
    | .undef  => return false -- TODO: should we do something smarter here?
  else
    return false

private structure AnalyzeResult where
  max?            : Option Expr := none
  hasUncomparable : Bool := false -- `true` if there are two types `α` and `β` where we don't have coercions in any direction.

private def isUnknow : Expr → Bool
  | .mvar ..        => true
  | .app f _        => isUnknow f
  | .letE _ _ _ b _ => isUnknow b
  | .mdata _ b      => isUnknow b
  | _                   => false

private def analyze (t : Tree) (expectedType? : Option Expr) : TermElabM AnalyzeResult := do
  let max? ←
    match expectedType? with
    | none => pure none
    | some expectedType =>
      let expectedType ← instantiateMVars expectedType
      if isUnknow expectedType then pure none else pure (some expectedType)
  (go t *> get).run' { max? }
where
   go (t : Tree) : StateRefT AnalyzeResult TermElabM Unit := do
     unless (← get).hasUncomparable do
       match t with
       | .op _ _ _ _ lhs rhs => go lhs; go rhs
       | .term _ _ val =>
         let type ← instantiateMVars (← inferType val)
         unless isUnknow type do
           match (← get).max? with
           | none     => modify fun s => { s with max? := type }
           | some max =>
             unless (← withNewMCtxDepth <| isDefEqGuarded max type) do
               if (← hasCoe type max) then
                 return ()
               else if (← hasCoe max type) then
                 modify fun s => { s with max? := type }
               else
                 trace[Elab.binop] "uncomparable types: {max}, {type}"
                 modify fun s => { s with hasUncomparable := true }

private def mkOp (f : Expr) (lhs rhs : Expr) : TermElabM Expr := do
  elabAppArgs f #[] #[Arg.expr lhs, Arg.expr rhs] (expectedType? := none) (explicit := false) (ellipsis := false) (resultIsOutParamSupport := false)

private def toExprCore (t : Tree) : TermElabM Expr := do
  match t with
  | .term _ trees e =>
    modifyInfoState (fun s => { s with trees := s.trees ++ trees }); return e
  | .op ref macroName true f lhs rhs  =>
    withRef ref <| withInfoContext' ref (mkInfo := mkTermInfo macroName ref) do
      mkOp f (← toExprCore lhs) (← mkFunUnit (← toExprCore rhs))
  | .op ref macroName false f lhs rhs =>
    withRef ref <| withInfoContext' ref (mkInfo := mkTermInfo macroName ref) do
      mkOp f (← toExprCore lhs) (← toExprCore rhs)

/--
  Auxiliary function to decide whether we should coerce `f`'s argument to `maxType` or not.
  - `f` is a binary operator.
  - `lhs == true` (`lhs == false`) if are trying to coerce the left-argument (right-argument).
  This function assumes `f` is a heterogeneous operator (e.g., `HAdd.hAdd`, `HMul.hMul`, etc).
  It returns true IF
  - `f` is a constant of the form `Cls.op` where `Cls` is a class name, and
  - `maxType` is of the form `C ...` where `C` is a constant, and
  - There are more than one default instance. That is, it assumes the class `Cls` for the heterogeneous operator `f`, and
    always has the monomorphic instance. (e.g., for `HAdd`, we have `instance [Add α] : HAdd α α α`), and
  - If `lhs == true`, then there is a default instance of the form `Cls _ (C ..) _`, and
  - If `lhs == false`, then there is a default instance of the form `Cls (C ..) _ _`.

  The motivation is to support default instances such as
  ```
  @[defaultInstance high]
  instance [Mul α] : HMul α (Array α) (Array α) where
    hMul a as := as.map (a * ·)

  #eval 2 * #[3, 4, 5]
  ```
  If the type of an argument is unknown we should not coerce it to `maxType` because it would prevent
  the default instance above from being even tried.
-/
private def hasHeterogeneousDefaultInstances (f : Expr) (maxType : Expr) (lhs : Bool) : MetaM Bool := do
  let .const fName .. := f | return false
  let .const typeName .. := maxType.getAppFn | return false
  let className := fName.getPrefix
  let defInstances ← getDefaultInstances className
  if defInstances.length ≤ 1 then return false
  for (instName, _) in defInstances do
    if let .app (.app (.app _heteroClass lhsType) rhsType) _resultType :=
        (← getConstInfo instName).type.getForallBody then
      if  lhs && rhsType.isAppOf typeName then return true
      if !lhs && lhsType.isAppOf typeName then return true
  return false

/--
  Return `true` if polymorphic function `f` has a homogenous instance of `maxType`.
  The coercions to `maxType` only makes sense if such instance exists.

  For example, suppose `maxType` is `Int`, and `f` is `HPow.hPow`. Then,
  adding coercions to `maxType` only make sense if we have an instance `HPow Int Int Int`.
-/
private def hasHomogeneousInstance (f : Expr) (maxType : Expr) : MetaM Bool := do
  let .const fName .. := f | return false
  let className := fName.getPrefix
  try
    let inst ← mkAppM className #[maxType, maxType, maxType]
    return (← trySynthInstance inst) matches .some _
  catch _ =>
    return false

mutual
  /--
    Try to coerce elements in the `t` to `maxType` when needed.
    If the type of an element in `t` is unknown we only coerce it to `maxType` if `maxType` does not have heterogeneous
    default instances. This extra check is approximated by `hasHeterogeneousDefaultInstances`.

    Remark: If `maxType` does not implement heterogeneous default instances, we do want to assign unknown types `?m` to
    `maxType` because it produces better type information propagation. Our test suite has many tests that would break if
    we don't do this. For example, consider the term
    ```
    eq_of_isEqvAux a b hsz (i+1) (Nat.succ_le_of_lt h) heqv.2
    ```
    `Nat.succ_le_of_lt h` type depends on `i+1`, but `i+1` only reduces to `Nat.succ i` if we know that `1` is a `Nat`.
    There are several other examples like that in our test suite, and one can find them by just replacing the
    `← hasHeterogeneousDefaultInstances f maxType lhs` test with `true`


    Remark: if `hasHeterogeneousDefaultInstances` implementation is not good enough we should refine it in the future.
  -/
  private partial def applyCoe (t : Tree) (maxType : Expr) (isPred : Bool) : TermElabM Tree := do
    go t none false isPred
  where
    go (t : Tree) (f? : Option Expr) (lhs : Bool) (isPred : Bool) : TermElabM Tree := do
      match t with
      | .op ref macroName lazy f lhs rhs =>
        /-
          We only keep applying coercions to `maxType` if `f` is predicate or
          `f` has a homogenous instance with `maxType`. See `hasHomogeneousInstance` for additional details.

          Remark: We assume `binrel%` elaborator is only used with homogenous predicates.
        -/
        if (← pure isPred <||> hasHomogeneousInstance f maxType) then
          return Tree.op ref macroName lazy f (← go lhs f true false) (← go rhs f false false)
        else
          let r ← withRef ref <| withInfoContext' ref (mkInfo := mkTermInfo macroName ref) do
            mkOp f (← toExpr lhs none) (← toExpr rhs none)
          let infoTrees ← getResetInfoTrees
          return .term ref infoTrees r
      | .term ref trees e =>
        let type ← instantiateMVars (← inferType e)
        trace[Elab.binop] "visiting {e} : {type} =?= {maxType}"
        if isUnknow type then
          if let some f := f? then
            if (← hasHeterogeneousDefaultInstances f maxType lhs) then
              -- See comment at `hasHeterogeneousDefaultInstances`
              return t
        if (← isDefEqGuarded maxType type) then
          return t
        else
          trace[Elab.binop] "added coercion: {e} : {type} => {maxType}"
          withRef ref <| return .term ref trees (← mkCoe maxType type e)

  private partial def toExpr (tree : Tree) (expectedType? : Option Expr) : TermElabM Expr := do
    let r ← analyze tree expectedType?
    trace[Elab.binop] "hasUncomparable: {r.hasUncomparable}, maxType: {r.max?}"
    if r.hasUncomparable || r.max?.isNone then
      let result ← toExprCore tree
      ensureHasType expectedType? result
    else
      let result ← toExprCore (← applyCoe tree r.max?.get! (isPred := false))
      trace[Elab.binop] "result: {result}"
      ensureHasType expectedType? result

end

@[builtinTermElab binop]
def elabBinOp : TermElab :=  fun stx expectedType? => do
  toExpr (← toTree stx) expectedType?

@[builtinTermElab binop_lazy]
def elabBinOpLazy : TermElab := elabBinOp

/--
  Elaboration functionf for `binrel%` and `binrel_no_prop%` notations.
  We use the infrastructure for `binop%` to make sure we propagate information between the left and right hand sides
  of a binary relation.

  Recall that the `binrel_no_prop%` notation is used for relations such as `==` which do not support `Prop`, but
  we still want to be able to write `(5 > 2) == (2 > 1)`.
-/
def elabBinRelCore (noProp : Bool) (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr :=  do
  match (← resolveId? stx[1]) with
  | some f => withSynthesizeLight do
    /-
    We used to use `withSynthesize (mayPostpone := true)` here instead of `withSynthesizeLight` here.
    Recall that `withSynthesizeLight` is equivalent to `withSynthesize (mayPostpone := true) (synthesizeDefault := false)`.
    It seems too much to apply default instances at binary relations. For example, we cannot elaborate
    ```
    def as : List Int := [-1, 2, 0, -3, 4]
    #eval as.map fun a => ite (a ≥ 0) [a] []
    ```
    The problem is that when elaborating `a ≥ 0` we don't know yet that `a` is an `Int`.
    Then, by applying default instances, we apply the default instance to `0` that forces it to become an `Int`,
    and Lean infers that `a` has type `Nat`.
    Then, later we get a type error because `as` is `List Int` instead of `List Nat`.
    This behavior is quite counterintuitive since if we avoid this elaborator by writing
    ```
    def as : List Int := [-1, 2, 0, -3, 4]
    #eval as.map fun a => ite (GE.ge a 0) [a] []
    ```
    everything works.
    However, there is a drawback of using `withSynthesizeLight` instead of `withSynthesize (mayPostpone := true)`.
    The following cannot be elaborated
    ```
    have : (0 == 1) = false := rfl
    ```
    We get a type error at `rfl`. `0 == 1` only reduces to `false` after we have applied the default instances that force
    the numeral to be `Nat`. We claim this is defensible behavior because the same happens if we do not use this elaborator.
    ```
    have : (BEq.beq 0 1) = false := rfl
    ```
    We can improve this failure in the future by applying default instances before reporting a type mismatch.
    -/
    let lhs ← withRef stx[2] <| toTree stx[2]
    let rhs ← withRef stx[3] <| toTree stx[3]
    let tree := Tree.op (lazy := false) stx .anonymous f lhs rhs
    let r ← analyze tree none
    trace[Elab.binrel] "hasUncomparable: {r.hasUncomparable}, maxType: {r.max?}"
    if r.hasUncomparable || r.max?.isNone then
      -- Use default elaboration strategy + `toBoolIfNecessary`
      let lhs ← toExprCore lhs
      let rhs ← toExprCore rhs
      let lhs ← toBoolIfNecessary lhs
      let rhs ← toBoolIfNecessary rhs
      let lhsType ← inferType lhs
      let rhs ← ensureHasType lhsType rhs
      elabAppArgs f #[] #[Arg.expr lhs, Arg.expr rhs] expectedType? (explicit := false) (ellipsis := false) (resultIsOutParamSupport := false)
    else
      let mut maxType := r.max?.get!
      /- If `noProp == true` and `maxType` is `Prop`, then set `maxType := Bool`. `See toBoolIfNecessary` -/
      if noProp then
        if (← withNewMCtxDepth <| isDefEq maxType (mkSort levelZero)) then
          maxType := Lean.mkConst ``Bool
      let result ← toExprCore (← applyCoe tree maxType (isPred := true))
      trace[Elab.binrel] "result: {result}"
      return result
  | none   => throwUnknownConstant stx[1].getId
where
  /-- If `noProp == true` and `e` has type `Prop`, then coerce it to `Bool`. -/
  toBoolIfNecessary (e : Expr) : TermElabM Expr := do
    if noProp then
      -- We use `withNewMCtxDepth` to make sure metavariables are not assigned
      if (← withNewMCtxDepth <| isDefEq (← inferType e) (mkSort levelZero)) then
        return (← ensureHasType (Lean.mkConst ``Bool) e)
    return e

@[builtinTermElab binrel] def elabBinRel : TermElab := elabBinRelCore false

@[builtinTermElab binrel_no_prop] def elabBinRelNoProp : TermElab := elabBinRelCore true

@[builtinTermElab defaultOrOfNonempty]
def elabDefaultOrNonempty : TermElab :=  fun stx expectedType? => do
  tryPostponeIfNoneOrMVar expectedType?
  match expectedType? with
  | none => throwError "invalid 'default_or_ofNonempty%', expected type is not known"
  | some expectedType =>
    try
      mkDefault expectedType
    catch ex => try
      mkOfNonempty expectedType
    catch _ =>
      if stx[1].isNone then
        throw ex
      else
        -- It is in the context of an `unsafe` constant. We can use sorry instead.
        -- Another option is to make a recursive application since it is unsafe.
        mkSorry expectedType false

builtin_initialize
  registerTraceClass `Elab.binop
  registerTraceClass `Elab.binrel

end BinOp

end Lean.Elab.Term
