import Lean

namespace Aeneas.Meta.PartialConfig

open Lean Elab Command

/-!
## `declare_command_partial_config_elab`

This command builds on top of `declare_command_config_elab` to enable elaboration
of partial configurations, while giving the possibility of setting the default values
of the omitted fields globally, by means of options.

Given a structure `Config` with default-valued fields and names
`elabFnName`, `PartialConfig`, `toConfig`, `optionNamePrefix`, the command

```
declare_command_partial_config_elab Config elabFnName PartialConfig toConfig optionNamePrefix
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

declare_command_partial_config_elab Config elabPartialConfig PartialConfig toConfig optionNamePrefix
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
declare_command_partial_config_elab Config elabFn PartialConfig toConfig optionNamePrefix
```

Generates a `PartialConfig` structure, the config elaborator, option registrations,
and a `PartialConfig.toConfig` conversion function.
-/
syntax (name := declareCommandPartialConfigElab)
    "declare_command_partial_config_elab "
    ident   -- Config                (existing source structure)
    ident   -- elabFn                (name for the generated elaboration function)
    ident   -- PartialConfig         (name for the generated partial structure)
    ident   -- toConfig              (base name for the conversion function)
    ident   -- optionNamePrefix      (prefix for registered options)
    : command

open Meta in
private def elabDeclareCommandPartialConfigElab
    (configId elabFnId partialConfigId toConfigId optionNamePrefixId : Syntax)
    : CommandElabM Unit := do
  let elabFnName   := elabFnId.getId
  let partialName  := partialConfigId.getId
  let toConfigName := toConfigId.getId
  let optionNamePrefix := optionNamePrefixId.getId

  -- ── Resolve `configName` in the current namespace/scope ───────────────────────
  let configName ← liftTermElabM <| resolveGlobalConstNoOverload configId

  -- ── Sanity check ────────────────────────────────────────────────────────────
  let env ← getEnv
  unless isStructure env configName do
    throwErrorAt configId "'{configName}' is not a structure"

  -- ── Collect field info: (fieldName, type, defaultValue) ──────────────
  let fieldNames := getStructureFields env configName
  let fieldData ← fieldNames.mapM fun fname => do
    let projName := configName ++ fname
    let type ← liftTermElabM <| getFieldTypeAsSyntax projName
    let defaultValue ← liftTermElabM <| getFieldDefaultValueAsSyntax configName fname
    return (fname, type, defaultValue)

  -- ── 1. `structure PartialConfig where` ──────────────────────────────────────
  let partialFields ← fieldData.mapM fun (fname, typeSyn, _) => do
    let fid := mkIdent fname
    `(Lean.Parser.Command.structExplicitBinder|
        ($fid : Option $typeSyn := none))
  let structCmd ← `(structure $(mkIdent partialName) where
                        $partialFields:structExplicitBinder*)
  elabCommand structCmd

  -- ── 2. `declare_command_config_elab elabFn PartialConfig` ───────────────────
  let dcceCmd ← `(declare_command_config_elab
                    $(mkIdent elabFnName) $(mkIdent partialName))
  elabCommand dcceCmd

  -- ── 3. `register_option` for each field ─────────────────────────────────────
  for (fname, type, defaultValue) in fieldData do
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
  -- TODO: name collisions
  let config   : TSyntax `ident := mkIdent `_config
  let options  : TSyntax `ident := mkIdent `_options

  /- For each field, generate:
     `let fi := Option.getD c.fi (Lean.Option.get optionNamePrefix.fi options)` -/
  let fieldBindings ← fieldData.mapM fun (fname, _, _) => do
    let fi       : TSyntax `ident := mkIdent fname
    let projId   : TSyntax `ident := mkIdent (partialName ++ fname)
    let fieldOptionId : TSyntax `ident := mkIdent (optionNamePrefix ++ fname)
    `(doElem| let $fi:ident := Option.getD ($projId:ident $config) ((_root_.Lean.Option.get $options $fieldOptionId:ident)))

  -- Build `pure (Config.mk f1 f2 ...)`
  let fieldIdents : Array (TSyntax `term) := fieldData.map fun field =>
    ⟨mkIdent field.1⟩
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
  | `(declare_command_partial_config_elab
        $configId $elabFnId $partialConfigId $toConfigId $optionNamePrefixId) =>
    elabDeclareCommandPartialConfigElab
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
declare_command_partial_config_elab Config elabPartialConfig PartialConfig toConfig Aeneas.Meta.PartialConfig.optionNamePrefix

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
fun {m} [Monad m] [MonadOptions m] _config => do
  let _options ← getOptions
  have x : Nat := _config.x.getD (Lean.Option.get _options Aeneas.Meta.PartialConfig.optionNamePrefix.x)
  have b : Bool := _config.b.getD (Lean.Option.get _options Aeneas.Meta.PartialConfig.optionNamePrefix.b)
  have n : String := _config.n.getD (Lean.Option.get _options Aeneas.Meta.PartialConfig.optionNamePrefix.n)
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
