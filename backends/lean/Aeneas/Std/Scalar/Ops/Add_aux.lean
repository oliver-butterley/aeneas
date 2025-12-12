import Aeneas.Std.Scalar.Ops.Add
import Aeneas.Mvcgen
import Std.Do
import Std.Tactic.Do

namespace Aeneas.Std

open Result Error Arith ScalarElab Std.Do

/-
Original theorems use macros `uscalar @[progress]` and `iscalar @[progress]`
which expand to theorems for all unsigned/signed scalar types.

@[progress]
theorem UScalar.add_spec {ty} {x y : UScalar ty}
  (hmax : ↑x + ↑y ≤ UScalar.max ty) :
  ∃ z, x + y = ok z ∧ (↑z : Nat) = ↑x + ↑y

@[progress]
theorem IScalar.add_spec {ty} {x y : IScalar ty}
  (hmin : IScalar.min ty ≤ ↑x + ↑y)
  (hmax : ↑x + ↑y ≤ IScalar.max ty) :
  ∃ z, x + y = ok z ∧ (↑z : Int) = ↑x + ↑y
-/

@[spec]
theorem UScalar.add_spec' {ty} {x y : UScalar ty}
    (hmax : ↑x + ↑y ≤ UScalar.max ty) :
    ⦃⌜True⌝⦄
    UScalar.add x y
    ⦃⇓z => ⌜(↑z : Nat) = ↑x + ↑y⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

@[spec]
theorem IScalar.add_spec' {ty} {x y : IScalar ty}
    (hmin : IScalar.min ty ≤ ↑x + ↑y)
    (hmax : ↑x + ↑y ≤ IScalar.max ty) :
    ⦃⌜True⌝⦄
    IScalar.add x y
    ⦃⇓z => ⌜(↑z : Int) = ↑x + ↑y⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

/-
Original:
uscalar @[progress] theorem «%S».add_spec {x y : «%S»} (hmax : x.val + y.val ≤ «%S».max) :
  ∃ z, x + y = ok z ∧ (↑z : Nat) = ↑x + ↑y :=
  UScalar.add_spec (by scalar_tac)
-/
uscalar @[spec] theorem «%S».add_spec' {x y : «%S»} (hmax : x.val + y.val ≤ «%S».max) :
    ⦃⌜True⌝⦄ UScalar.add x y ⦃⇓z => ⌜(↑z : Nat) = ↑x + ↑y⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

/-
Original:
iscalar @[progress] theorem «%S».add_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x + ↑y) (hmax : ↑x + ↑y ≤ «%S».max) :
  ∃ z, x + y = ok z ∧ (↑z : Int) = ↑x + ↑y :=
  IScalar.add_spec (by scalar_tac) (by scalar_tac)
-/
iscalar @[spec] theorem «%S».add_spec' {x y : «%S»}
    (hmin : «%S».min ≤ ↑x + ↑y) (hmax : ↑x + ↑y ≤ «%S».max) :
    ⦃⌜True⌝⦄ IScalar.add x y ⦃⇓z => ⌜(↑z : Int) = ↑x + ↑y⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

end Aeneas.Std
