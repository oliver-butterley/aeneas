import Lean

namespace Aeneas.Meta.PartialConfig

open Lean Elab Command

/- The code in this section is adapted from `Lean.Elab.Tactic.Config`: it does the same thing but allows notation
`+field` (or `-field`) for fields of type `Option Bool` and not only `Bool`. We need this for `declare_elab_partial_config`.

TODO: find a way of upstreaming the diff, which is very small.
TODO: we initially tried to write `declare_partial_config_elab` by piggy-backing on `declare_elab_config`, but as we
had to implement our own version of `declare_elab_config` there is no point in keeping all the complexity of
`declare_partial_config_elab`, in particular there is no need to define the `PartialConfig` structure anymore.
-/
namespace OptionConfig

  open Meta Parser.Tactic Command

  private def expandFieldName (structName : Name) (fieldName : Name) : MetaM (Name × Name) := do
    let env ← getEnv
    unless isStructure env structName do throwError "`{.ofConstName structName}` is not a structure"
    let some baseStructName := findField? env structName fieldName
      | throwError "Structure `{.ofConstName structName}` does not have a field named `{fieldName}`"
    let some path := getPathToBaseStructure? env baseStructName structName
      | throwError "Internal error: Failed to access field `{fieldName}` in parent structure"
    let field := path.foldl (init := .anonymous) (fun acc s => Name.appendCore acc <| Name.mkSimple s.getString!) ++ fieldName
    let fieldInfo := (getFieldInfo? env baseStructName fieldName).get!
    return (field, fieldInfo.projFn)

  private partial def expandField (structName : Name) (field : Name) : MetaM (Name × Name) := do
    match field with
    | .num .. | .anonymous => throwError m!"Invalid configuration field"
    | .str .anonymous fieldName => expandFieldName structName (Name.mkSimple fieldName)
    | .str field' fieldName =>
      let (field', projFn) ← expandField structName field'
      let notStructure {α} : MetaM α := throwError "Field `{field'}` of structure `{.ofConstName structName}` is not a structure"
      let .const structName' _ := (← getConstInfo projFn).type.getForallBody | notStructure
      unless isStructure (← getEnv) structName' do notStructure
      let (field'', projFn) ← expandFieldName structName' (Name.mkSimple fieldName)
      return (field' ++ field'', projFn)

  /-- Elaborates a tactic configuration. -/
  def elabConfig (recover : Bool) (structName : Name) (items : Array Lean.Elab.Tactic.ConfigItemView) : TermElabM Expr :=
    withoutModifyingStateWithInfoAndMessages <| withLCtx {} {} <| withSaveInfoContext do
      let mkStructInst (source? : Option Term) (fields : TSyntaxArray ``Parser.Term.structInstField) : TermElabM Term :=
        match source? with
        | some source => `({$source with $fields* : $(mkCIdent structName)})
        | none        => `({$fields* : $(mkCIdent structName)})
      let mut source? : Option Term := none
      let mut seenFields : NameSet := {}
      let mut fields : TSyntaxArray ``Parser.Term.structInstField := #[]
      for item in items do
        try
          let option := item.option.getId.eraseMacroScopes
          if option == `config then
            unless fields.isEmpty do
              -- Flush fields. Even though these values will not be used, we still want to elaborate them.
              source? ← mkStructInst source? fields
              seenFields := {}
              fields := #[]
            let valSrc ← withRef item.value `(($item.value : $(mkCIdent structName)))
            if let some source := source? then
              source? ← withRef item.value `({$valSrc, $source with : $(mkCIdent structName)})
            else
              source? := valSrc
          else
            addCompletionInfo <| CompletionInfo.fieldId item.option option {} structName
            let (path, projFn) ← withRef item.option <| expandField structName option
            if item.bool then
              -- DIFF: this is the only diff with the code in `Lean.Elab.Tactic.Config`
              -- Verify that the type is `Option Bool`
              let projFn ← getConstInfo projFn
              let body := projFn.type.bindingBody!
              unless body.isAppOfArity ``Option 1 && body.getArg! 0 == .const ``Bool [] do
                throwErrorAt item.ref m!"Option is not boolean-valued, so `({option} := ...)` syntax must be used"
            let value ←
              match item.value with
              | `(by $seq:tacticSeq) =>
                -- Special case: `(opt := by tacs)` uses the `tacs` syntax itself
                withRef item.value <| `(Unhygienic.run `(tacticSeq| $seq))
              | value => pure value
            if seenFields.contains path then
              -- Flush fields. There is a duplicate, but we still want to elaborate both.
              source? ← mkStructInst source? fields
              seenFields := {}
              fields := #[]
            fields := fields.push <| ← `(Parser.Term.structInstField|
              $(mkCIdentFrom item.option path (canonical := true)):ident := $value)
            seenFields := seenFields.insert path
        catch ex =>
          if recover then
            logException ex
          else
            throw ex
      let stx : Term ← mkStructInst source? fields
      let e ← Term.withSynthesize <| Term.elabTermEnsuringType stx (mkConst structName)
      instantiateMVars e

  section
  -- We automatically disable the following option for `macro`s but the subsequent `def` both contains
  -- a quotation and is called only by `macro`s, so we disable the option for it manually. Note that
  -- we can't use `in` as it is parsed as a single command and so the option would not influence the
  -- parser.
  set_option internal.parseQuotWithCurrentStage false

  private meta def mkConfigElaborator
      (doc? : Option (TSyntax ``Parser.Command.docComment)) (elabName type monadName : Ident)
      (adapt recover : Term) : MacroM (TSyntax `command) := do
    let empty ← withRef type `({ : $type})
    `(unsafe def evalUnsafe (e : Expr) : TermElabM $type :=
        Meta.evalExpr' (safety := .unsafe) $type ``$type e
      @[implemented_by evalUnsafe] opaque eval (e : Expr) : TermElabM $type
      $[$doc?:docComment]?
      def $elabName (optConfig : Syntax) : $monadName $type := $adapt do
        let recover := $recover
        let go : TermElabM $type := withRef optConfig do
          let items := Lean.Elab.Tactic.mkConfigItemViews (getConfigItems optConfig)
          if items.isEmpty then
            return $empty
          unless (← getEnv).contains ``$type do
            throwError m!"Error evaluating configuration: Environment does not yet contain type {``$type}"
          recordExtraModUseFromDecl (isMeta := true) ``$type
          let c ← elabConfig recover ``$type items
          if c.hasSyntheticSorry then
            -- An error is already logged, return the default.
            return $empty
          if c.hasSorry then
            throwError m!"Configuration contains `sorry`"
          try
            let res ← eval c
            return res
          catch ex =>
            let msg := m!"Error evaluating configuration\n{indentD c}\n\nException: {ex.toMessageData}"
            if false then
              logError msg
              return $empty
            else
              throwError msg
        go)

  end

end OptionConfig

/-!
`declare_config_elab elabName TypeName` declares a function `elabName : Syntax → TacticM TypeName`
that elaborates a tactic configuration.
The tactic configuration can be from `Lean.Parser.Tactic.optConfig` or `Lean.Parser.Tactic.config`,
and these can also be wrapped in null nodes (for example, from `(config)?`).

The elaborator responds to the current recovery state.

For defining elaborators for commands, use `declare_command_config_elab`.
-/
macro (name := configElab) doc?:(docComment)? "declare_config_option_elab" elabName:ident type:ident : command => do
  OptionConfig.mkConfigElaborator doc? elabName type (Lean.mkCIdent ``Lean.Elab.Tactic.TacticM) (Lean.mkCIdent ``id) (← `((← read).recover))


/-!
## `declare_partial_config_elab`

This command builds on top of `declare_command_config_elab` to enable elaboration
of partial configurations, while giving the possibility of setting the default values
of the omitted fields globally, by means of options.

Given a structure `Config` with default-valued fields and names
`elabFnName`, `PartialConfig`, `toConfig`, `optionNamePrefix`, the command

```
declare_partial_config_elab Config elabFnName PartialConfig toConfig optionNamePrefix
```

generates code which:

1. defines a `structure PartialConfig`, which has the same fields as `Config` but each wrapped in `Option`,
   defaulting to `none`.
2. inserts the command `declare_command_config_elab elabFnName PartialConfig` to register the partial elaboration for `PartialConfig`
3. for each field `f : T` of `Config`, inserts the command `register_option optionNamePrefix.f : T`, whose
   `defValue` is `Config`'s own default value.
4. defines the function `def PartialConfig.toConfig` which converts a `PartialConfig` to a `Config` by filling the
   omitted fields (i.e., fields equal to `none`) with the default values registered in the options.

Example:
```
structure Config where
  x : Nat := 3
  b : Bool := true
  n : String := ""

declare_partial_config_elab Config elabPartialConfig PartialConfig toConfig optionNamePrefix
-- Generates:

structure PartialConfig where
  x : Option Nat := none
  b : Option Bool := none
  n : Option String := none

declare_command_config_elab elabPartialConfig PartialConfig

register_option optionNamePrefix.x : Nat := {
  defValue := 3 -- the default value of Config.x
  descr    := "The default value of `Config.x`"
}

register_option optionNamePrefix.b : Bool := {
  defValue := true -- the default value of Config.b
  descr    := "The default value of `Config.b`"
}

register_option optionNamePrefix.n : String := {
  defValue := "" -- the default value of Config.b
  descr    := "The default value of `Config.n`"
}

def PartialConfig.toConfig {m} [Monad m] [self : Lean.MonadOptions m] (c : PartialConfig) : m Config := do
  let options ← Lean.MonadOptions.getOptions
  let { x, b, n } := c
  let x := x.getD (optionNamePrefix.x.get options)
  let b := b.getD (optionNamePrefix.b.get options)
  let n := n.getD (optionNamePrefix.n.get options)
  pure { x, b, n}
```
-/

-- ──────────────────────────────────────────────────────────────────────────────
-- Helpers
-- ──────────────────────────────────────────────────────────────────────────────

/-- Name of the auto-generated default-value declaration for a structure field. -/
private def fieldDefaultName (structName fieldName : Name) : Name :=
  structName ++ (fieldName ++ `_default)

open Meta in
/-- Retrieve the default value of a structure field as a `TSyntax term`. -/
private def getFieldDefaultValueAsSyntax (structName fieldName : Name) : MetaM (TSyntax `term) := do
  let env ← getEnv
  let declName := fieldDefaultName structName fieldName
  let some info := env.find? declName
    | throwError "No default-value declaration found for \
                  '{structName}.{fieldName}'. \
                  Make sure every field has a default value."
  let val ← reduce info.value!
  match val with
  | .lit (.natVal n) => return Syntax.mkNumLit (toString n)
  | .lit (.strVal s) => return Syntax.mkStrLit s
  | .const ``Bool.true  _ => return mkIdent ``true
  | .const ``Bool.false _ => return mkIdent ``false
  | _ => throwError "Unsupported default-value kind for \
                     '{structName}.{fieldName}': {val}"

open Meta in
/-- Retrieve the (non-dependent) type of a structure field as a `TSyntax term`. -/
private def getFieldTypeAsSyntax (projName : Name) : TermElabM (TSyntax `term) := do
  let info ← getConstInfo projName
  -- info.type : (self : Struct) → FieldType   (possibly universe-polymorphic)
  forallTelescopeReducing info.type fun _ ty =>
    PrettyPrinter.delab ty

-- ──────────────────────────────────────────────────────────────────────────────
-- Syntax
-- ──────────────────────────────────────────────────────────────────────────────

/--
```
declare_partial_config_elab Config elabFn PartialConfig toConfig optionNamePrefix
```

Generates a `PartialConfig` structure, the config elaborator, option registrations,
and a `PartialConfig.toConfig` conversion function.
-/
syntax (name := declareCommandPartialConfigElab)
    "declare_partial_config_elab "
    ident   -- Config                (existing source structure)
    ident   -- elabFn                (name for the generated elaboration function)
    ident   -- PartialConfig         (name for the generated partial structure)
    ident   -- toConfig              (base name for the conversion function)
    ident   -- optionNamePrefix      (prefix for registered options)
    : command

open Meta in
private def elabDeclarePartialConfigElab
    (configId elabFnId partialConfigId toConfigId optionNamePrefixId : Syntax)
    : CommandElabM Unit := do
  let elabFnName   := elabFnId.getId
  let partialName  := partialConfigId.getId
  let toConfigName := toConfigId.getId
  let optionNamePrefix := optionNamePrefixId.getId

  let config   : TSyntax `ident := mkIdent (← liftCoreM (mkFreshUserName `config))
  let options  : TSyntax `ident := mkIdent (← liftCoreM (mkFreshUserName `options))

  -- ── Resolve `configName` in the current namespace/scope ───────────────────────
  let configName ← liftTermElabM <| resolveGlobalConstNoOverload configId

  -- ── Sanity check ────────────────────────────────────────────────────────────
  let env ← getEnv
  unless isStructure env configName do
    throwErrorAt configId "'{configName}' is not a structure"

  -- ── Collect field info: (varName, fieldName, type, defaultValue) ──────────────
  let fieldNames := getStructureFields env configName
  let fieldData ← fieldNames.mapM fun fname => do
    let projName := configName ++ fname
    let type ← liftTermElabM <| getFieldTypeAsSyntax projName
    let defaultValue ← liftTermElabM <| getFieldDefaultValueAsSyntax configName fname
    let varName ← liftCoreM (mkFreshUserName fname)
    return (varName, fname, type, defaultValue)

  -- ── 1. `structure PartialConfig where` ──────────────────────────────────────
  let partialFields ← fieldData.mapM fun (_, fname, typeSyn, _) => do
    let fid := mkIdent fname
    `(Lean.Parser.Command.structExplicitBinder|
        ($fid : Option $typeSyn := none))
  let structCmd ← `(structure $(mkIdent partialName) where
                        $partialFields:structExplicitBinder*)
  elabCommand structCmd

  -- ── 2. `declare_command_config_elab elabFn PartialConfig` ───────────────────
  let dcceCmd ← `(declare_config_option_elab
                    $(mkIdent elabFnName) $(mkIdent partialName))
  elabCommand dcceCmd

  -- ── 3. `register_option` for each field ─────────────────────────────────────
  for (_, fname, type, defaultValue) in fieldData do
    let optId    := mkIdent (optionNamePrefix ++ fname)
    let descr := Syntax.mkStrLit s!"The default value of `{configName}.{fname}`"
    let regCmd ← `(register_option $optId : $type := {
      defValue := $defaultValue
      descr    := $descr
    })
    elabCommand regCmd

  -- ── 4. `def PartialConfig.toConfig` ─────────────────────────────────────────
  /-
  ```
  def PartialConfig.toConfig {m} [Monad m] [Lean.MonadOptions m]
      (c : PartialConfig) : m Config := do
    let options ← Lean.MonadOptions.getOptions
    let x := Option.getD (Config.x c) (Lean.Option.get options optionNamePrefix.x)
    let b := Option.getD (Config.b c) (Lean.Option.get options optionNamePrefix.b)
    let n := Option.getD (Config.n c) (Lean.Option.get options optionNamePrefix.n)
    pure (Config.mk x b n)
  ```
  -/

  /- For each field, generate:
     `let fi := Option.getD c.fi (Lean.Option.get optionNamePrefix.fi options)` -/
  let fieldBindings ← fieldData.mapM fun (varName, fname, _, _) => do
    let varName  :TSyntax `ident := mkIdent varName
    let projId   : TSyntax `ident := mkIdent (partialName ++ fname)
    let fieldOptionId : TSyntax `ident := mkIdent (optionNamePrefix ++ fname)
    `(doElem| let $varName:ident := Option.getD ($projId:ident $config) ((_root_.Lean.Option.get $options $fieldOptionId:ident)))

  -- Build `pure (Config.mk f1 f2 ...)`
  let fieldIdents : Array (TSyntax `term) := fieldData.map fun (varName, _) =>
    ⟨mkIdent varName⟩
  let pureDo ← `(doElem| pure (⟨ $fieldIdents,* ⟩))

  -- `let options ← Lean.MonadOptions.getOptions`
  let getOptsDo ← `(doElem| let $(options) ← Lean.MonadOptions.getOptions)

  -- Put all the elements together to generate the function body
  let allElems : Array (TSyntax `doElem) :=
    #[getOptsDo] ++ fieldBindings ++ #[pureDo]
  let allSeqItems ← allElems.mapM fun elem =>
    `(Lean.Parser.Term.doSeqItem| $elem:doElem)

  /- Generate the function declaration:
     `fn PartialConfig.toConfig ... := ...` -/
  let fnId := mkIdent (partialName ++ toConfigName)
  let toConfigCmd ← `(
    def $fnId {m : Type → Type} [Monad m] [Lean.MonadOptions m]
        ($config : $(mkIdent partialName)) : m $(mkIdent configName) := do
      $allSeqItems*)
  elabCommand toConfigCmd

elab_rules : command
  | `(declare_partial_config_elab
        $configId $elabFnId $partialConfigId $toConfigId $optionNamePrefixId) =>
    elabDeclarePartialConfigElab
      configId elabFnId partialConfigId toConfigId optionNamePrefixId

-- ============================================================
-- Example
-- ============================================================
section Example

structure Config where
  x : Nat    := 3
  b : Bool   := true
  n : String := ""

-- Declare
declare_partial_config_elab Config elabPartialConfig PartialConfig toConfig Aeneas.Meta.PartialConfig.optionNamePrefix

/--
info: structure Aeneas.Meta.PartialConfig.PartialConfig : Type
number of parameters: 0
fields:
  Aeneas.Meta.PartialConfig.PartialConfig.x : Option Nat :=
    none
  Aeneas.Meta.PartialConfig.PartialConfig.b : Option Bool :=
    none
  Aeneas.Meta.PartialConfig.PartialConfig.n : Option String :=
    none
constructor:
  Aeneas.Meta.PartialConfig.PartialConfig.mk (x : Option Nat) (b : Option Bool) (n : Option String) : PartialConfig-/
#guard_msgs in
#print PartialConfig

/--
info: def Aeneas.Meta.PartialConfig.PartialConfig.toConfig : {m : Type → Type} →
  [Monad m] → [MonadOptions m] → PartialConfig → m Config :=
fun {m} [Monad m] [MonadOptions m] config => do
  let options ← getOptions
  have x : Nat := config.x.getD (Lean.Option.get options Aeneas.Meta.PartialConfig.optionNamePrefix.x)
  have b : Bool := config.b.getD (Lean.Option.get options Aeneas.Meta.PartialConfig.optionNamePrefix.b)
  have n : String := config.n.getD (Lean.Option.get options Aeneas.Meta.PartialConfig.optionNamePrefix.n)
  pure { x := x, b := b, n := n }
-/
#guard_msgs in
#print PartialConfig.toConfig

/-- info: Aeneas.Meta.PartialConfig.Aeneas.Meta.PartialConfig.optionNamePrefix.x : Lean.Option Nat -/
#guard_msgs in
#check Aeneas.Meta.PartialConfig.optionNamePrefix.x

/-- info: Aeneas.Meta.PartialConfig.Aeneas.Meta.PartialConfig.optionNamePrefix.b : Lean.Option Bool -/
#guard_msgs in
#check Aeneas.Meta.PartialConfig.optionNamePrefix.b

/-- info: Aeneas.Meta.PartialConfig.Aeneas.Meta.PartialConfig.optionNamePrefix.n : Lean.Option String -/
#guard_msgs in
#check Aeneas.Meta.PartialConfig.optionNamePrefix.n   -- : Lean.Option String-/

end Example

end Aeneas.Meta.PartialConfig
