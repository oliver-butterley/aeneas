import Aeneas.Std.Scalar.Ops.Rem
import Aeneas.Mvcgen
import Std.Do
import Std.Tactic.Do

namespace Aeneas.Std

open Result Error Arith ScalarElab Std.Do

/-
Original theorems use macros `uscalar @[progress]` and `iscalar @[progress]`

uscalar @[progress] theorem «%S».rem_spec (x : «%S») {y : «%S»} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Nat) = ↑x % ↑y

iscalar @[progress] theorem «%S».rem_spec (x : «%S») {y : «%S»} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Int) = Int.tmod ↑x ↑y
-/

@[spec]
theorem UScalar.rem_spec' {ty} (x : UScalar ty) {y : UScalar ty}
    (hnz : y.val ≠ 0) :
    ⦃⌜True⌝⦄
    UScalar.rem x y
    ⦃⇓z => ⌜(↑z : Nat) = ↑x % ↑y⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

@[spec]
theorem IScalar.rem_spec' {ty} (x : IScalar ty) {y : IScalar ty}
    (hnz : y.val ≠ 0) :
    ⦃⌜True⌝⦄
    IScalar.rem x y
    ⦃⇓z => ⌜(↑z : Int) = Int.tmod ↑x ↑y⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

/-
Original:
uscalar @[progress] theorem «%S».rem_spec (x : «%S») {y : «%S»} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Nat) = ↑x % ↑y :=
  UScalar.rem_spec (by scalar_tac)
-/
uscalar @[spec] theorem «%S».rem_spec' (x : «%S») {y : «%S»} (hnz : y.val ≠ 0) :
    ⦃⌜True⌝⦄ UScalar.rem x y ⦃⇓z => ⌜(↑z : Nat) = ↑x % ↑y⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

/-
Original:
iscalar @[progress] theorem «%S».rem_spec (x : «%S») {y : «%S»} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Int) = Int.tmod ↑x ↑y :=
  IScalar.rem_spec (by scalar_tac)
-/
iscalar @[spec] theorem «%S».rem_spec' (x : «%S») {y : «%S»} (hnz : y.val ≠ 0) :
    ⦃⌜True⌝⦄ IScalar.rem x y ⦃⇓z => ⌜(↑z : Int) = Int.tmod ↑x ↑y⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

end Aeneas.Std
