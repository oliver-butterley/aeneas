import Aeneas.Std.Scalar.Ops.Div
import Aeneas.Mvcgen
import Std.Do
import Std.Tactic.Do

namespace Aeneas.Std

open Result Error Arith ScalarElab Std.Do

/-
Original theorems use macros `uscalar @[progress]` and `iscalar @[progress]`

uscalar @[progress] theorem «%S».div_spec (x : «%S») {y : «%S»} (hnz : ↑y ≠ (0 : Nat)) :
  ∃ z, x / y = ok z ∧ (↑z : Nat) = ↑x / ↑y

iscalar @[progress] theorem «%S».div_spec {x y : «%S»} (hnz : ↑y ≠ (0 : Int))
  (hNoOverflow : ¬ (x.val = «%S».min ∧ y.val = -1)) :
  ∃ z, x / y = ok z ∧ (↑z : Int) = Int.tdiv ↑x ↑y
-/

@[spec]
theorem UScalar.div_spec' {ty} (x : UScalar ty) {y : UScalar ty}
    (hnz : y.val ≠ 0) :
    ⦃⌜True⌝⦄
    UScalar.div x y
    ⦃⇓z => ⌜(↑z : Nat) = ↑x / ↑y⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

@[spec]
theorem IScalar.div_spec' {ty} {x y : IScalar ty}
    (hnz : y.val ≠ 0)
    (hNoOverflow : ¬ (x.val = IScalar.min ty ∧ y.val = -1)) :
    ⦃⌜True⌝⦄
    IScalar.div x y
    ⦃⇓z => ⌜(↑z : Int) = Int.tdiv ↑x ↑y⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

/-
Original:
uscalar @[progress] theorem «%S».div_spec (x : «%S») {y : «%S»} (hnz : ↑y ≠ (0 : Nat)) :
  ∃ z, x / y = ok z ∧ (↑z : Nat) = ↑x / ↑y :=
  UScalar.div_spec (by scalar_tac)
-/
uscalar @[spec] theorem «%S».div_spec' (x : «%S») {y : «%S»} (hnz : ↑y ≠ (0 : Nat)) :
    ⦃⌜True⌝⦄ UScalar.div x y ⦃⇓z => ⌜(↑z : Nat) = ↑x / ↑y⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

/-
Original:
iscalar @[progress] theorem «%S».div_spec {x y : «%S»} (hnz : ↑y ≠ (0 : Int))
  (hNoOverflow : ¬ (x.val = «%S».min ∧ y.val = -1)) :
  ∃ z, x / y = ok z ∧ (↑z : Int) = Int.tdiv ↑x ↑y :=
  IScalar.div_spec (by scalar_tac) (by scalar_tac) (by scalar_tac)
-/
iscalar @[spec] theorem «%S».div_spec' {x y : «%S»} (hnz : ↑y ≠ (0 : Int))
    (hNoOverflow : ¬ (x.val = «%S».min ∧ y.val = -1)) :
    ⦃⌜True⌝⦄ IScalar.div x y ⦃⇓z => ⌜(↑z : Int) = Int.tdiv ↑x ↑y⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

end Aeneas.Std
