import Aeneas.Std.Scalar.Ops.Mul
import Aeneas.Mvcgen
import Std.Do
import Std.Tactic.Do

namespace Aeneas.Std

open Result Error Arith ScalarElab Std.Do

/-
Original theorems use macros `uscalar @[progress]` and `iscalar @[progress]`

uscalar @[progress] theorem «%S».mul_spec {x y : «%S»} (hmax : x.val * y.val ≤ «%S».max) :
  ∃ z, x * y = ok z ∧ (↑z : Nat) = ↑x * ↑y

iscalar @[progress] theorem «%S».mul_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x * ↑y) (hmax : ↑x * ↑y ≤ «%S».max) :
  ∃ z, x * y = ok z ∧ (↑z : Int) = ↑x * ↑y
-/

@[spec]
theorem UScalar.mul_spec' {ty} {x y : UScalar ty}
    (hmax : ↑x * ↑y ≤ UScalar.max ty) :
    ⦃⌜True⌝⦄
    UScalar.mul x y
    ⦃⇓z => ⌜(↑z : Nat) = ↑x * ↑y⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

@[spec]
theorem IScalar.mul_spec' {ty} {x y : IScalar ty}
    (hmin : IScalar.min ty ≤ ↑x * ↑y)
    (hmax : ↑x * ↑y ≤ IScalar.max ty) :
    ⦃⌜True⌝⦄
    IScalar.mul x y
    ⦃⇓z => ⌜(↑z : Int) = ↑x * ↑y⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

/-
Original:
uscalar @[progress] theorem «%S».mul_spec {x y : «%S»} (hmax : x.val * y.val ≤ «%S».max) :
  ∃ z, x * y = ok z ∧ (↑z : Nat) = ↑x * ↑y :=
  UScalar.mul_spec (by scalar_tac)
-/
uscalar @[spec] theorem «%S».mul_spec' {x y : «%S»} (hmax : x.val * y.val ≤ «%S».max) :
    ⦃⌜True⌝⦄ UScalar.mul x y ⦃⇓z => ⌜(↑z : Nat) = ↑x * ↑y⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

/-
Original:
iscalar @[progress] theorem «%S».mul_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x * ↑y) (hmax : ↑x * ↑y ≤ «%S».max) :
  ∃ z, x * y = ok z ∧ (↑z : Int) = ↑x * ↑y :=
  IScalar.mul_spec (by scalar_tac) (by scalar_tac)
-/
iscalar @[spec] theorem «%S».mul_spec' {x y : «%S»}
    (hmin : «%S».min ≤ ↑x * ↑y) (hmax : ↑x * ↑y ≤ «%S».max) :
    ⦃⌜True⌝⦄ IScalar.mul x y ⦃⇓z => ⌜(↑z : Int) = ↑x * ↑y⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

end Aeneas.Std
