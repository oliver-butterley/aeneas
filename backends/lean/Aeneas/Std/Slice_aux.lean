import Aeneas.Std.Slice
import Aeneas.Mvcgen
import Std.Do
import Std.Tactic.Do

namespace Aeneas.Std

open Result Error core.ops.range Std.Do

/-
Original:
@[progress]
theorem Slice.index_usize_spec {α : Type u} [Inhabited α] (v: Slice α) (i: Usize)
  (hbound : i.val < v.length) :
  ∃ x, v.index_usize i = ok x ∧ x = v.val[i.val]! := by
  simp only [index_usize]
  simp only [length, getElem?_Usize_eq, exists_eq_right] at *
  simp only [List.getElem?_eq_getElem, List.getElem!_eq_getElem?_getD, Option.getD_some, hbound]
-/
@[spec]
theorem Slice.index_usize_spec' {α : Type u} [Inhabited α] (v : Slice α) (i : Usize)
    (hbound : i.val < v.length) :
    ⦃⌜True⌝⦄
    v.index_usize i
    ⦃⇓x => ⌜x = v.val[i.val]!⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

/-
Original:
@[progress]
theorem Slice.update_spec {α : Type u} (v: Slice α) (i: Usize) (x : α)
  (hbound : i.val < v.length) :
  ∃ nv, v.update i x = ok nv ∧
  nv = v.set i x
  := by
  simp only [update, set]
  simp at *
  simp [*]
-/
@[spec]
theorem Slice.update_spec' {α : Type u} (v : Slice α) (i : Usize) (x : α)
    (hbound : i.val < v.length) :
    ⦃⌜True⌝⦄
    v.update i x
    ⦃⇓nv => ⌜nv = v.set i x⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

/-
Original:
@[progress]
theorem Slice.index_mut_usize_spec {α : Type u} [Inhabited α] (v: Slice α) (i: Usize)
  (hbound : i.val < v.length) :
  ∃ x, v.index_mut_usize i = ok (x, Slice.set v i) ∧
  x = v.val[i.val]! := by
  simp only [index_mut_usize, Bind.bind, bind]
  have ⟨ x, h ⟩ := Slice.index_usize_spec v i hbound
  simp [h]
-/
@[spec]
theorem Slice.index_mut_usize_spec' {α : Type u} [Inhabited α] (v : Slice α) (i : Usize)
    (hbound : i.val < v.length) :
    ⦃⌜True⌝⦄
    v.index_mut_usize i
    ⦃⇓r => ⌜r = (v.val[i.val]!, Slice.set v i)⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

/-
Original:
@[progress]
theorem Slice.subslice_spec {α : Type u} [Inhabited α] (s : Slice α) (r : Range Usize)
  (h0 : r.start.val < r.end_.val) (h1 : r.end_.val ≤ s.val.length) :
  ∃ ns, subslice s r = ok ns ∧
  ns.val = s.slice r.start.val r.end_.val ∧
  (∀ i, i + r.start.val < r.end_.val → ns[i]! = s[r.start.val + i]!)
  := by
  simp_all only [subslice, length, and_self, ite_true, ok.injEq, slice, exists_eq_left', true_and]
  intro i _
  have := List.getElem!_slice r.start.val r.end_.val i s.val (by scalar_tac)
  simp only [List.getElem!_eq_getElem?_getD, getElem!_Nat_eq] at *
  apply this
-/
@[spec]
theorem Slice.subslice_spec' {α : Type u} [Inhabited α] (s : Slice α) (r : Range Usize)
    (h0 : r.start.val < r.end_.val) (h1 : r.end_.val ≤ s.val.length) :
    ⦃⌜True⌝⦄
    Slice.subslice s r
    ⦃⇓ns => ⌜ns.val = s.slice r.start.val r.end_.val ∧
             (∀ i, i + r.start.val < r.end_.val → ns[i]! = s[r.start.val + i]!)⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

/-
Original:
@[progress]
theorem Slice.update_subslice_spec {α : Type u} [Inhabited α] (a : Slice α) (r : Range Usize) (ss : Slice α)
  (_ : r.start.val < r.end_.val) (_ : r.end_.val ≤ a.length) (_ : ss.length = r.end_.val - r.start.val) :
  ∃ na, update_subslice a r ss = ok na ∧
  (∀ i, i < r.start.val → na[i]! = a[i]!) ∧
  (∀ i, r.start.val ≤ i → i < r.end_.val → na[i]! = ss[i - r.start.val]!) ∧
  (∀ i, r.end_.val ≤ i → i < a.length → na[i]! = a[i]!) := by
  simp only [update_subslice, length, and_self, ↓reduceDIte, ok.injEq, getElem!_Nat_eq,
    exists_eq_left', *]
  simp_lists
-/
@[spec]
theorem Slice.update_subslice_spec' {α : Type u} [Inhabited α] (a : Slice α) (r : Range Usize) (ss : Slice α)
    (h0 : r.start.val < r.end_.val) (h1 : r.end_.val ≤ a.length) (h2 : ss.length = r.end_.val - r.start.val) :
    ⦃⌜True⌝⦄
    Slice.update_subslice a r ss
    ⦃⇓na => ⌜(∀ i, i < r.start.val → na[i]! = a[i]!) ∧
             (∀ i, r.start.val ≤ i → i < r.end_.val → na[i]! = ss[i - r.start.val]!) ∧
             (∀ i, r.end_.val ≤ i → i < a.length → na[i]! = a[i]!)⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

/-
Original:
@[progress]
theorem Slice.clone_spec {T : Type} {clone : T → Result T} {s : Slice T} (h : ∀ x ∈ s.val, clone x = ok x) :
  Slice.clone clone s = ok s := by
  simp only [Slice.clone]
  have ⟨ l', h ⟩ := List.clone_spec h
  simp [h]
-/
-- To do (Oliver): doesn't fit the standard pattern for `spec` (no existential result)

/-
Original:
@[progress]
theorem core.slice.index.SliceIndexRangeUsizeSlice.index_mut.progress_spec (r : core.ops.range.Range Usize) (s : Slice α)
  (h0 : r.start ≤ r.end_) (h1 : r.end_ ≤ s.length) :
  ∃ s1 index_mut_back, core.slice.index.SliceIndexRangeUsizeSlice.index_mut r s = ok (s1, index_mut_back) ∧
  s1.val = s.val.slice r.start r.end_ ∧
  s1.length = r.end_ - r.start ∧
  ∀ s2, s2.length = s1.length → index_mut_back s2 = s.setSlice! r.start.val s2 := by
  simp only [index_mut, UScalar.le_equiv, Slice.length, dite_eq_ite]
  split
  . simp only [ok.injEq, Prod.mk.injEq, and_assoc, exists_and_left, exists_eq_left', true_and]
    simp_lists
    simp_scalar
    simp_lists [Slice.eq_iff]
  . simp only [reduceCtorEq, false_and, exists_false]
    scalar_tac
-/
@[spec]
theorem core.slice.index.SliceIndexRangeUsizeSlice.index_mut.progress_spec' (r : core.ops.range.Range Usize) (s : Slice α)
    (h0 : r.start ≤ r.end_) (h1 : r.end_ ≤ s.length) :
    ⦃⌜True⌝⦄
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut r s
    ⦃⇓result => ⌜result.1.val = s.val.slice r.start r.end_ ∧
                 result.1.length = r.end_ - r.start ∧
                 ∀ s2, s2.length = result.1.length → result.2 s2 = s.setSlice! r.start.val s2⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

/-
Original:
@[progress]
theorem core.slice.Slice.copy_from_slice.progress_spec (copyInst : core.marker.Copy α) (s0 s1 : Slice α)
  (h : s0.length = s1.length) :
  core.slice.Slice.copy_from_slice copyInst s0 s1 = ok s1 := by
  simp only [copy_from_slice, ite_eq_left_iff, UScalar.neq_to_neq_val, Usize.ofNat_val_eq, h,
    Slice.length, not_true_eq_false, reduceCtorEq, imp_self]
-/
-- To do (Oliver): doesn't fit the standard pattern for `spec` (no existential result)

end Aeneas.Std
