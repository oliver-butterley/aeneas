import Lean
import Lean.Elab.Tactic.Config
import Lean.Elab.Eval

namespace Aeneas.Meta.PartialConfig

open Lean Elab Command Term Meta PrettyPrinter

/-!
# `declare_partial_config_elab`

Usage:
```lean
structure Config where
  n : Nat  := 3
  b : Bool := false

declare_partial_config_elab Config elabConfig myTool
```

Generates:
- Persistent options `myTool.n`, `myTool.b` (via `initialize`).
- An elaborator:
    `def elabConfig (cfg : TSyntax `Lean.Parser.Tactic.optConfig) : TermElabM Config`
-/

-- ---------------------------------------------------------------------------
-- OptConfig decomposition
-- ---------------------------------------------------------------------------

/-- Decompose a `TSyntax \`Lean.Parser.Tactic.optConfig` into `(fieldName, valueSyntax)` pairs.
    - `+field` → `(field, true)`
    - `-field` → `(field, false)`
    - `(field := val)` → `(field, val)` -/
partial def decomposeOptConfig (cfg : TSyntax `Lean.Parser.Tactic.optConfig) :
    Array (Name × Syntax) :=
  go cfg.raw #[]
where
  go (s : Syntax) (acc : Array (Name × Syntax)) : Array (Name × Syntax) :=
    match s with
    | .node _ `Lean.Parser.Tactic.posConfigItem #[_, name] =>
      if name.isIdent then acc.push (name.getId, mkIdent `true) else acc
    | .node _ `Lean.Parser.Tactic.negConfigItem #[_, name] =>
      if name.isIdent then acc.push (name.getId, mkIdent `false) else acc
    | .node _ `Lean.Parser.Tactic.valConfigItem #[_, name, _, val, _] =>
      if name.isIdent then acc.push (name.getId, val) else acc
    | .node _ _ children => children.foldl (fun a c => go c a) acc
    | _ => acc

-- ---------------------------------------------------------------------------
-- Tests for decomposeOptConfig
-- ---------------------------------------------------------------------------

section DecomposeOptConfigTests

/-- Tactic that prints each config entry it receives. -/
elab "test_config" cfg:Lean.Parser.Tactic.optConfig : tactic => do
  let entries := decomposeOptConfig cfg
  if entries.isEmpty then
    Lean.logInfo "No config entries."
  else
    for (name, val) in entries do
      Lean.logInfo m!"{name} := {val}"

/-- Helper tactic to show the raw syntax tree of an optConfig. -/
elab "showOptConfigSyntax" cfg:Lean.Parser.Tactic.optConfig : tactic =>
  Lean.logInfo m!"{repr cfg.raw}"

-- Expected output:
--   foo := false
--   bar := 42
--   baz := true
example : True := by
  test_config -foo (bar := 42) +baz
  trivial

example : True := by
  showOptConfigSyntax -foo (bar := 42) +baz
  trivial

end DecomposeOptConfigTests

-- ---------------------------------------------------------------------------
-- Struct field info
-- ---------------------------------------------------------------------------

private def collectFieldInfo (structName : Name) :
    MetaM (Array (Name × Expr × Expr)) := do
  let env ← getEnv
  let some si := getStructureInfo? env structName
    | throwError "not a structure: {structName}"
  let mut out : Array (Name × Expr × Expr) := #[]
  for field in si.fieldNames do
    let some defFnName := getDefaultFnForField? env structName field
      | throwError "field '{structName}.{field}' has no default value"
    let defFnInfo ← getConstInfo defFnName
    let defVal    ← reduce (mkConst defFnName)
    out := out.push (field, defFnInfo.type, defVal)
  return out

-- ---------------------------------------------------------------------------
-- Syntax
-- ---------------------------------------------------------------------------

syntax (name := declarePartialConfigElab)
  "declare_partial_config_elab" ident ident ident : command

-- ---------------------------------------------------------------------------
-- Elaborator
-- ---------------------------------------------------------------------------

elab_rules : command
  | `(declare_partial_config_elab $structId $elabFnId $optPrefixId) => do
    let ns         ← getCurrNamespace
    let structName := ns ++ structId.getId
    let elabFnName := elabFnId.getId
    let optPrefix  := optPrefixId.getId

    let fields ← liftTermElabM (collectFieldInfo structName)

    -- ── 1. Register options ───────────────────────────────────────────────────
    for (field, ty, defVal) in fields do
      let optName := optPrefix ++ field
      let alreadyExists ← liftCoreM do
        return (← getOptionDecls).contains optName
      if alreadyExists then continue
      let tySx  : Term ← liftTermElabM (delab ty)
      let defSx : Term ← liftTermElabM (delab defVal)
      let descr := "Default value for field " ++ structName.toString ++ "." ++ field.toString
      elabCommand (← `(command|
        initialize $(mkIdent optName) : Lean.Option $tySx ←
          Lean.Option.register $(Lean.quote optName)
            { defValue := $defSx, descr := $(Lean.quote descr) }))

    -- ── 2. Public elaborator ─────────────────────────────────────────────────
    --
    -- Strategy:
    --   a. Use `decomposeOptConfig` to get `Array (Name × Syntax)` from the cfg.
    --   b. For each field (unrolled at macro time), pick the user value or fall
    --      back to `Option.get opts optName`.
    --   c. Build a `{ f1 := v1, … }` struct literal and call
    --      `elabTermEnsuringType` + `evalExpr` once.
    --
    -- `evalExpr` is unsafe; hidden behind a single `@[implemented_by]`.

    let helperTy    : Term ← `(Lean.Elab.Term.TermElabM $(mkIdent structName))
    let optConfigTy : Term ← `(Lean.TSyntax `Lean.Parser.Tactic.optConfig)
    let implName     := elabFnName ++ `impl
    let structNameQ  : Term := Lean.quote structName

    -- For each field i, generate at macro time:
    --   _fb{i} : Term  ← delab (toExpr (Option.get opts optName))
    --   _v{i}  : Term   = match pairs.find? field with
    --                      | some (_, valStx) => ⟨valStx⟩
    --                      | none             => _fb{i}
    -- Then build ⟨_v0, _v1, …⟩ and elaborate it.
    let nFields   := fields.size
    let fbNames   : Array Name := (Array.range nFields).map fun i => .mkSimple s!"_fb{i}"
    let slotNames : Array Name := (Array.range nFields).map fun i => .mkSimple s!"_v{i}"

    -- Per-field fallback: Term for `Option.get opts optName` (typed value)
    let fbBindings : Array Term ← fields.mapIdxM fun i (_, _, _) => do
      let (field, _, _) := fields[i]!
      let optName := optPrefix ++ field
      `(Lean.Option.get opts $(mkIdent optName))

    -- Per-field slot: picks user Syntax or fallback Term
    let fieldValExprs : Array Term ← fields.mapIdxM fun i (field, _, _) => do
      let fieldQ : Term := Lean.quote field
      let fbId   : Term := mkIdent fbNames[i]!
      `(match (pairs.find? fun p => p.1 == $fieldQ) with
        | some (_, valStx) => TSyntax.mk valStx
        | none             => $fbId)

    -- Build ⟨_v0, _v1, …⟩ struct literal
    let slotTerms : Array Term := slotNames.map fun n => (mkIdent n : Term)
    -- Build the constructor application as Syntax at runtime using mkAppStx,
    -- since the slot Terms are runtime values that can't be macro-spliced.
    -- We emit: Lean.Syntax.mkApp (mkIdent ``MyConfig.mk) (Array.mk [_v0, _v1, …])
    let ctorQ : Term := Lean.quote (structName ++ `mk)
    let structLit : Term ←
      `(Lean.Syntax.mkApp (Lean.mkIdent $ctorQ) (Array.mk [$slotTerms,*]))

    -- Build bindings as doSeqItem for $[...]* splicing in do-blocks.
    let valBinds : Array (TSyntax `Lean.Parser.Term.doSeqItem) ←
      (slotNames.zip fieldValExprs).mapM fun (slotName, rhs) =>
        `(Lean.Parser.Term.doSeqItem| let $(mkIdent slotName) : Lean.Term := $rhs)
    let fbBinds : Array (TSyntax `Lean.Parser.Term.doSeqItem) ←
      (fbNames.zip fbBindings).mapM fun (fbName, rhs) =>
        `(Lean.Parser.Term.doSeqItem|
            let $(mkIdent fbName) : Lean.Term ←
              Lean.PrettyPrinter.delab (Lean.toExpr $rhs))

    let implBody : Term ← `(do
      let pairs := decomposeOptConfig cfg
      let opts  ← Lean.getOptions
      $[$(fbBinds)]*
      $[$(valBinds)]*
      let ty   := Lean.mkConst $structNameQ
      let expr ← Lean.Elab.Term.elabTermEnsuringType $structLit ty
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let expr ← Lean.instantiateMVars expr
      Lean.Meta.evalExpr $(mkIdent structName) ty expr)

    elabCommand (← `(command|
      private unsafe def $(mkIdent implName)
          (cfg : $optConfigTy) : $helperTy := $implBody))
    elabCommand (← `(command|
      @[implemented_by $(mkIdent implName)]
      opaque $(mkIdent elabFnName)
          (cfg : $optConfigTy) : $helperTy))

-- ---------------------------------------------------------------------------
-- Smoke test
-- ---------------------------------------------------------------------------

namespace Example

structure MyConfig where
  n    : Nat    := 3
  b    : Bool   := false
  name : String := "hello"

declare_partial_config_elab MyConfig elabMyConfig myTool

#check @elabMyConfig
-- elabMyConfig : TSyntax `Lean.Parser.Tactic.optConfig → TermElabM MyConfig

end Example

end Aeneas.Meta.PartialConfig
