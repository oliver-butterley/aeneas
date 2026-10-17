module
public import Aeneas.Std.Core.Ops
public import Aeneas.Std.Core.Result
public meta import Aeneas.Tactic.Step.Init

public section

namespace Aeneas.Std

open Result

/-- Model of `Result::map` (<https://doc.rust-lang.org/std/result/enum.Result.html#method.map>,
    `library/core/src/result.rs`): maps the payload of `Ok` through `fnOnce` and leaves `Err`
    untouched. The closure is called exactly once on `Ok`, and never on `Err`. -/
@[expose, rust_fun "core::result::{core::result::Result<@T, @E>}::map"]
def core.result.Result.map
  {T E U F : Type _} (fnOnce : core.ops.function.FnOnce F T U)
  (x : core.result.Result T E) (f : F) :
  Std.Result (core.result.Result U E) :=
  match x with
  | .Ok value => do
      let mapped ← fnOnce.call_once f value
      ok (.Ok mapped)
  | .Err error => ok (.Err error)

-- Note: the lemmas are named after the constructors (`map_Ok`/`map_Err`) because
-- `core.result.Result.map_err` is already the model of `Result::map_err`.
@[simp]
theorem core.result.Result.map_Ok
  {T E U F : Type _} (fnOnce : core.ops.function.FnOnce F T U) (value : T) (f : F) :
  core.result.Result.map fnOnce (.Ok value : core.result.Result T E) f = (do
    let mapped ← fnOnce.call_once f value
    ok (core.result.Result.Ok mapped : core.result.Result U E)) := rfl

@[simp]
theorem core.result.Result.map_Err
  {T E U F : Type _} (fnOnce : core.ops.function.FnOnce F T U) (error : E) (f : F) :
  core.result.Result.map fnOnce (.Err error : core.result.Result T E) f =
    ok (core.result.Result.Err error : core.result.Result U E) := rfl

/-- Step spec for `Result::map`: `post` is the postcondition of the closure, which
    `step` can infer with `+inferPost`. -/
@[step]
theorem core.result.Result.map.spec {T E U F : Type _}
  (fnOnce : core.ops.function.FnOnce F T U) (x : core.result.Result T E) (f : F)
  {post : T → U → Prop}
  (hf : ∀ value, x = .Ok value → fnOnce.call_once f value ⦃ post value ⦄) :
  core.result.Result.map fnOnce x f ⦃ y =>
    match x with
    | .Err error => y = .Err error
    | .Ok value => ∃ mapped, y = .Ok mapped ∧ post value mapped ⦄ := by
  cases x with
  | Err error => simp [core.result.Result.map]
  | Ok value =>
    simp only [core.result.Result.map]
    apply WP.spec_bind (hf value rfl)
    intro mapped h
    simp [h]

/-- Pure model of `Result::map_err`: leaves `Ok` untouched and maps the payload
    of `Err` through `fnOnce`. -/
@[expose, rust_fun "core::result::{core::result::Result<@T, @E>}::map_err"]
def core.result.Result.map_err
  {T E F O : Type _} (fnOnce : core.ops.function.FnOnce O E F)
  (x : core.result.Result T E) (f : O) :
  Std.Result (core.result.Result T F) :=
  match x with
  | .Ok value => ok (.Ok value)
  | .Err error => do
      let mapped ← fnOnce.call_once f error
      ok (.Err mapped)

@[simp]
theorem core.result.Result.map_err_ok
  {T E F O : Type _} (fnOnce : core.ops.function.FnOnce O E F) (value : T) (f : O) :
  core.result.Result.map_err fnOnce (.Ok value) f =
    ok (core.result.Result.Ok value : core.result.Result T F) := rfl

@[simp]
theorem core.result.Result.map_err_err
  {T E F O : Type _} (fnOnce : core.ops.function.FnOnce O E F) (error : E) (f : O) :
  core.result.Result.map_err fnOnce
      (core.result.Result.Err error : core.result.Result T E) f = (do
    let mapped ← fnOnce.call_once f error
    ok (core.result.Result.Err mapped : core.result.Result T F)) := rfl

/-- Pure model of `Result::unwrap_or`: the payload of `Ok`, or `default` on
    `Err`. -/
@[expose, step_pure_def, rust_fun "core::result::{core::result::Result<@T, @E>}::unwrap_or" -canFail]
def core.result.Result.unwrap_or {T E : Type _} (x : core.result.Result T E) (default : T) : T :=
  match x with
  | .Ok value => value
  | .Err _ => default

@[simp]
theorem core.result.Result.unwrap_or_ok {T E : Type _} (value default : T) :
  core.result.Result.unwrap_or (.Ok value : core.result.Result T E) default = value := rfl

@[simp]
theorem core.result.Result.unwrap_or_err {T E : Type _} (error : E) (default : T) :
  core.result.Result.unwrap_or (.Err error : core.result.Result T E) default = default := rfl

end Aeneas.Std
