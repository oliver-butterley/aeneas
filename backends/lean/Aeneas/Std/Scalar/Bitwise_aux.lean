import Aeneas.Std.Scalar.Bitwise
import Aeneas.Mvcgen
import Std.Do
import Std.Tactic.Do

namespace Aeneas.Std

open Result Error Arith ScalarElab Std.Do

/-
Bitwise operations use macros `uscalar @[progress]` for shift operations.
The and/or operations have generic specs.
-/

/-
Original:
@[progress]
theorem UScalar.and_spec {ty} (x y : UScalar ty) :
  ∃ z, toResult (x &&& y) = ok z ∧
  z.val = (x &&& y).val ∧
  z.bv = x.bv &&& y.bv
-/
@[spec]
theorem UScalar.and_spec' {ty} (x y : UScalar ty) :
    ⦃⌜True⌝⦄
    toResult (x &&& y)
    ⦃⇓z => ⌜z.val = (x &&& y).val ∧ z.bv = x.bv &&& y.bv⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

/-
Original:
@[progress]
theorem UScalar.or_spec {ty} (x y : UScalar ty) :
  ∃ z, toResult (x ||| y) = ok z ∧ z.val = (x ||| y).val ∧ z.bv = x.bv||| y.bv
-/
@[spec]
theorem UScalar.or_spec' {ty} (x y : UScalar ty) :
    ⦃⌜True⌝⦄
    toResult (x ||| y)
    ⦃⇓z => ⌜z.val = (x ||| y).val ∧ z.bv = x.bv ||| y.bv⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

/-
Original:
@[progress]
theorem IScalar.and_spec {ty} (x y : IScalar ty) :
  ∃ z, toResult (x &&& y) = ok z ∧ z.val = (x &&& y).val ∧ z.bv = x.bv &&& y.bv
-/
@[spec]
theorem IScalar.and_spec' {ty} (x y : IScalar ty) :
    ⦃⌜True⌝⦄
    toResult (x &&& y)
    ⦃⇓z => ⌜z.val = (x &&& y).val ∧ z.bv = x.bv &&& y.bv⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

/-
Original:
@[progress]
theorem IScalar.or_spec {ty} (x y : IScalar ty) :
  ∃ z, toResult (x ||| y) = ok z ∧ z.val = (x ||| y).val ∧ z.bv = x.bv||| y.bv
-/
@[spec]
theorem IScalar.or_spec' {ty} (x y : IScalar ty) :
    ⦃⌜True⌝⦄
    toResult (x ||| y)
    ⦃⇓z => ⌜z.val = (x ||| y).val ∧ z.bv = x.bv ||| y.bv⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

/-
Original:
uscalar @[progress] theorem «%S».ShiftRight_spec {ty1} (x : «%S») (y : UScalar ty1) (hy : y.val < %BitWidth) :
  ∃ (z : «%S»), x >>> y = ok z ∧ z.val = x.val >>> y.val ∧ z.bv = x.bv >>> y.val
  := by apply UScalar.ShiftRight_spec; simp [*]
-/
uscalar @[spec] theorem «%S».ShiftRight_spec' {ty1} (x : «%S») (y : UScalar ty1) (hy : y.val < %BitWidth) :
    ⦃⌜True⌝⦄ UScalar.shiftRight_UScalar x y ⦃⇓z => ⌜z.val = x.val >>> y.val ∧ z.bv = x.bv >>> y.val⌝⦄ := by
  sorry

/-
Original:
uscalar @[progress] theorem «%S».ShiftRight_IScalar_spec {ty1} (x : «%S») (y : IScalar ty1) (hy0 : 0 ≤ y.val) (hy : y.val < %BitWidth) :
  ∃ (z : «%S»), x >>> y = ok z ∧ z.val = x.val >>> y.toNat ∧ z.bv = x.bv >>> y.toNat
  := by apply UScalar.ShiftRight_IScalar_spec <;> simp [*]
-/
uscalar @[spec] theorem «%S».ShiftRight_IScalar_spec' {ty1} (x : «%S») (y : IScalar ty1) (hy0 : 0 ≤ y.val) (hy : y.val < %BitWidth) :
    ⦃⌜True⌝⦄ UScalar.shiftRight_IScalar x y ⦃⇓z => ⌜z.val = x.val >>> y.toNat ∧ z.bv = x.bv >>> y.toNat⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

/-
Original:
uscalar @[progress] theorem «%S».ShiftLeft_spec {ty1} (x : «%S») (y : UScalar ty1) (hy : y.val < %BitWidth) :
  ∃ (z : «%S»), x <<< y = ok z ∧ z.val = (x.val <<< y.val) % «%S».size ∧ z.bv = x.bv <<< y.val
  := by apply UScalar.ShiftLeft_spec <;> simp [*]
-/
uscalar @[spec] theorem «%S».ShiftLeft_spec' {ty1} (x : «%S») (y : UScalar ty1) (hy : y.val < %BitWidth) :
    ⦃⌜True⌝⦄ UScalar.shiftLeft_UScalar x y ⦃⇓z => ⌜z.val = (x.val <<< y.val) % «%S».size ∧ z.bv = x.bv <<< y.val⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

/-
Original:
uscalar @[progress] theorem «%S».ShiftLeft_IScalar_spec {ty1} (x : «%S») (y : IScalar ty1) (hy0 : 0 ≤ y.val) (hy : y.val < %BitWidth) :
  ∃ (z : «%S»), x <<< y = ok z ∧ z.val = (x.val <<< y.toNat) % «%S».size ∧ z.bv = x.bv <<< y.toNat
  := by apply UScalar.ShiftLeft_IScalar_spec <;> simp [*]
-/
uscalar @[spec] theorem «%S».ShiftLeft_IScalar_spec' {ty1} (x : «%S») (y : IScalar ty1) (hy0 : 0 ≤ y.val) (hy : y.val < %BitWidth) :
    ⦃⌜True⌝⦄ UScalar.shiftLeft_IScalar x y ⦃⇓z => ⌜z.val = (x.val <<< y.toNat) % «%S».size ∧ z.bv = x.bv <<< y.toNat⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

end Aeneas.Std
