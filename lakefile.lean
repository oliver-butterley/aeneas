import Lake
open Lake DSL

-- Important: mathlib imports std4 and quote4: we mustn't add a `require std4` line
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

package «aeneas» where
  preferReleaseBuild := true
  buildArchive := s!"lean-build-aeneas-{System.Platform.target}.tar.gz"
  -- Models of the Rust standard library mirror Rust paths (e.g. `core.clone.Clone.clone`)
  leanOptions := #[⟨`weak.linter.dupNamespace, false⟩]
  -- `lake test` builds the tests
  testDriver := "AeneasTests"

@[default_target] lean_lib «Aeneas» where
  srcDir := "backends/lean"

private def notCI : Bool := run_io
  return (← IO.getEnv "CI").isNone

@[default_target] lean_lib «AeneasMeta» where
  srcDir := "backends/lean"
  -- Precompiling modules triggers issues in CI so we deactivate this.
  precompileModules := notCI

/-- The Lean files generated from the Rust tests in `tests/src`, and their proofs.

Not a default target: only built by `lake test`, neither by users nor for the release. -/
lean_lib «AeneasTests» where
  srcDir := "tests/lean"
  globs := #[`AeneasTests.+]

/-- Generate the `.ml` file listing the definitions supported by the standard library. -/
lean_exe extract where
  srcDir := "backends/lean"
  root := `AeneasExtract
  supportInterpreter := true
  needs := #[`@/Aeneas]

/-- Extract the Lean tokens that are not permitted as standalone identifiers. -/
lean_exe extract_lean_keywords where
  srcDir := "backends/lean"
  root := `ExtractLeanKeywords
  supportInterpreter := true
  needs := #[`@/Aeneas]
