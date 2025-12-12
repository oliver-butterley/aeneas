import Aeneas.Std.Scalar.Ops.Sub
import Aeneas.Mvcgen
import Std.Do
import Std.Tactic.Do

namespace Aeneas.Std

open Result Error Arith ScalarElab Std.Do

/-
Original theorems use macros `uscalar @[progress]` and `iscalar @[progress]`

@[progress]
theorem UScalar.sub_spec {ty} {x y : UScalar ty}
  (h : y.val ≤ x.val) :
  ∃ z, x - y = ok z ∧ z.val = x.val - y.val ∧ y.val ≤ x.val

@[progress]
theorem IScalar.sub_spec {ty} {x y : IScalar ty}
  (hmin : IScalar.min ty ≤ ↑x - ↑y)
  (hmax : ↑x - ↑y ≤ IScalar.max ty) :
  ∃ z, x - y = ok z ∧ (↑z : Int) = ↑x - ↑y
-/

@[spec]
theorem UScalar.sub_spec' {ty} {x y : UScalar ty}
    (h : y.val ≤ x.val) :
    ⦃⌜True⌝⦄
    UScalar.sub x y
    ⦃⇓z => ⌜z.val = x.val - y.val ∧ y.val ≤ x.val⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

@[spec]
theorem IScalar.sub_spec' {ty} {x y : IScalar ty}
    (hmin : IScalar.min ty ≤ ↑x - ↑y)
    (hmax : ↑x - ↑y ≤ IScalar.max ty) :
    ⦃⌜True⌝⦄
    IScalar.sub x y
    ⦃⇓z => ⌜(↑z : Int) = ↑x - ↑y⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

/-
Original:
uscalar @[progress] theorem «%S».sub_spec {x y : «%S»} (h : y.val ≤ x.val) :
  ∃ z, x - y = ok z ∧ z.val = x.val - y.val ∧ y.val ≤ x.val :=
  UScalar.sub_spec h
-/
uscalar @[spec] theorem «%S».sub_spec' {x y : «%S»} (h : y.val ≤ x.val) :
    ⦃⌜True⌝⦄ UScalar.sub x y ⦃⇓z => ⌜z.val = x.val - y.val ∧ y.val ≤ x.val⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

/-
Original:
iscalar @[progress] theorem «%S».sub_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x - ↑y) (hmax : ↑x - ↑y ≤ «%S».max) :
  ∃ z, x - y = ok z ∧ (↑z : Int) = ↑x - ↑y :=
  IScalar.sub_spec (by scalar_tac) (by scalar_tac)
-/
iscalar @[spec] theorem «%S».sub_spec' {x y : «%S»}
    (hmin : «%S».min ≤ ↑x - ↑y) (hmax : ↑x - ↑y ≤ «%S».max) :
    ⦃⌜True⌝⦄ IScalar.sub x y ⦃⇓z => ⌜(↑z : Int) = ↑x - ↑y⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

end Aeneas.Std
