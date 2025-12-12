import Aeneas.Std.Scalar.CoreConvertNum
import Aeneas.Mvcgen
import Std.Do
import Std.Tactic.Do

namespace Aeneas.Std

open Result Error ScalarElab Std.Do

/-
Original:
uscalar_no_usize @[progress]
theorem core.num.«%S».to_le_bytes.progress_spec (x : «%S») :
  ∃ y, toResult (core.num.«%S».to_le_bytes x) = ok y ∧ y.val = x.bv.toLEBytes.map (@UScalar.mk UScalarTy.U8) := by
  simp only [toResult, to_le_bytes, UScalarTy.U8_numBits_eq, ok.injEq, exists_eq_left']
-/
uscalar_no_usize @[spec]
theorem core.num.«%S».to_le_bytes.spec' (x : «%S») :
    ⦃⌜True⌝⦄
    toResult (core.num.«%S».to_le_bytes x)
    ⦃⇓y => ⌜y.val = x.bv.toLEBytes.map (@UScalar.mk UScalarTy.U8)⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

/-
Original:
iscalar_no_isize @[progress]
theorem core.num.«%S».to_le_bytes.progress_spec (x : «%S») :
  ∃ y, toResult (core.num.«%S».to_le_bytes x) = ok y ∧ y.val = x.bv.toLEBytes.map (@IScalar.mk IScalarTy.I8) := by
  simp only [toResult, to_le_bytes, IScalarTy.I8_numBits_eq, ok.injEq, exists_eq_left']
-/
iscalar_no_isize @[spec]
theorem core.num.«%S».to_le_bytes.spec' (x : «%S») :
    ⦃⌜True⌝⦄
    toResult (core.num.«%S».to_le_bytes x)
    ⦃⇓y => ⌜y.val = x.bv.toLEBytes.map (@IScalar.mk IScalarTy.I8)⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

/-
Original:
uscalar_no_usize @[progress]
theorem core.num.«%S».from_le_bytes.progress_spec (x : Array U8 (%Size)#usize) :
  ∃ y, toResult (core.num.«%S».from_le_bytes x) = ok y ∧ y.bv = (BitVec.fromLEBytes (x.val.map U8.bv)).cast (by simp) := by
  simp only [toResult, from_le_bytes, ok.injEq, exists_eq_left']
-/
uscalar_no_usize @[spec]
theorem core.num.«%S».from_le_bytes.spec' (x : Array U8 (%Size)#usize) :
    ⦃⌜True⌝⦄
    toResult (core.num.«%S».from_le_bytes x)
    ⦃⇓y => ⌜y.bv = (BitVec.fromLEBytes (x.val.map U8.bv)).cast (by simp)⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

/-
Original:
iscalar_no_isize @[progress]
theorem core.num.«%S».from_le_bytes.progress_spec (x : Array I8 (%Size)#usize) :
  ∃ y, toResult (core.num.«%S».from_le_bytes x) = ok y ∧ y.bv = (BitVec.fromLEBytes (x.val.map I8.bv)).cast (by simp) := by
  simp only [toResult, from_le_bytes, ok.injEq, exists_eq_left']
-/
iscalar_no_isize @[spec]
theorem core.num.«%S».from_le_bytes.spec' (x : Array I8 (%Size)#usize) :
    ⦃⌜True⌝⦄
    toResult (core.num.«%S».from_le_bytes x)
    ⦃⇓y => ⌜y.bv = (BitVec.fromLEBytes (x.val.map I8.bv)).cast (by simp)⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

end Aeneas.Std
