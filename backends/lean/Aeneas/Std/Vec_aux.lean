import Aeneas.Std.Vec
import Aeneas.Mvcgen
import Std.Do
import Std.Tactic.Do

namespace Aeneas.Std

open Result Std.Do

namespace alloc.vec

/-
Original:
@[progress]
theorem Vec.push_spec {α : Type u} (v : Vec α) (x : α) (h : v.val.length < Usize.max) :
  ∃ v1, v.push x = ok v1 ∧
  v1.val = v.val ++ [x] := by
  rw [push]; simp
  split <;> simp_all
  scalar_tac
-/
@[spec]
theorem Vec.push_spec' {α : Type u} (v : Vec α) (x : α) (h : v.val.length < Usize.max) :
    ⦃⌜True⌝⦄
    v.push x
    ⦃⇓v1 => ⌜v1.val = v.val ++ [x]⌝⦄ := by
  rw [push]
  split
  · simp_all; mvcgen
  · simp_all; grind
-- To do (Oliver): strange proof but could close proof starting with mvcgen

/-
Original:
@[progress]
theorem Vec.insert_spec {α : Type u} (v: Vec α) (i: Usize) (x: α)
  (hbound : i.val < v.length) :
  ∃ nv, v.insert i x = ok nv ∧ nv.val = v.val.set i x := by
  simp [insert, *]
-/
@[spec]
theorem Vec.insert_spec' {α : Type u} (v : Vec α) (i : Usize) (x : α)
    (hbound : i.val < v.length) :
    ⦃⌜True⌝⦄
    v.insert i x
    ⦃⇓nv => ⌜nv.val = v.val.set i x⌝⦄ := by
  mvcgen [insert]

/-
Original:
@[progress]
theorem Vec.index_usize_spec {α : Type u} [Inhabited α] (v: Vec α) (i: Usize)
  (hbound : i.val < v.length) :
  ∃ x, v.index_usize i = ok x ∧ x = v.val[i.val]! := by
  simp only [index_usize]
  simp at *
  simp [*]
-/
@[spec]
theorem Vec.index_usize_spec' {α : Type u} [Inhabited α] (v : Vec α) (i : Usize)
    (hbound : i.val < v.length) :
    ⦃⌜True⌝⦄
    v.index_usize i
    ⦃⇓x => ⌜x = v.val[i.val]!⌝⦄ := by
  mvcgen [index_usize]
  · grind
  · sorry

/-
Original:
@[progress]
theorem Vec.update_spec {α : Type u} (v: Vec α) (i: Usize) (x : α)
  (hbound : i.val < v.length) :
  ∃ nv, v.update i x = ok nv ∧
  nv = v.set i x
  := by
  simp only [update, set]
  simp at *
  split <;> simp_all
-/
@[spec]
theorem Vec.update_spec' {α : Type u} (v : Vec α) (i : Usize) (x : α)
    (hbound : i.val < v.length) :
    ⦃⌜True⌝⦄
    v.update i x
    ⦃⇓nv => ⌜nv = v.set i x⌝⦄ := by
  mvcgen [update]
  grind

/-
Original:
@[progress]
theorem Vec.index_mut_usize_spec {α : Type u} [Inhabited α] (v: Vec α) (i: Usize)
  (hbound : i.val < v.length) :
  ∃ x, v.index_mut_usize i = ok (x, v.set i) ∧
  x = v.val[i.val]!
  := by
  simp only [index_mut_usize]
  have ⟨ x, h ⟩ := index_usize_spec v i hbound
  simp [h]
-/
@[spec]
theorem Vec.index_mut_usize_spec' {α : Type u} [Inhabited α] (v : Vec α) (i : Usize)
    (hbound : i.val < v.length) :
    ⦃⌜True⌝⦄
    v.index_mut_usize i
    ⦃⇓r => ⌜r = (v.val[i.val]!, v.set i)⌝⦄ := by
  mvcgen [index_mut_usize]
  · sorry
  · sorry
  · sorry

/-
Original:
@[progress]
theorem alloc.slice.Slice.to_vec_spec {T : Type} (cloneInst : core.clone.Clone T) (s : Slice T)
  (h : ∀ x ∈ s.val, cloneInst.clone x = ok x) :
  alloc.slice.Slice.to_vec cloneInst s = ok s := by
  simp only [to_vec]
  rw [Slice.clone_spec h]
-/
-- To do (Oliver): doesn't fit the standard pattern for `spec`

/-
Original:
@[progress]
theorem alloc.vec.from_elem_spec {T : Type} (cloneInst : core.clone.Clone T)
  (x : T) (n : Usize) (h : cloneInst.clone x = ok x) :
  ∃ v, alloc.vec.from_elem cloneInst x n = ok v ∧
  v.val = List.replicate n.val x ∧
  v.length = n.val := by
  unfold from_elem
  have ⟨ l, h ⟩ := @List.clone_spec _ cloneInst.clone (List.replicate n.val x) (by intros; simp_all)
  simp [h]
-/
@[spec]
theorem alloc.vec.from_elem_spec' {T : Type} (cloneInst : core.clone.Clone T)
    (x : T) (n : Usize) (h : cloneInst.clone x = ok x) :
    ⦃⌜True⌝⦄
    alloc.vec.from_elem cloneInst x n
    ⦃⇓v => ⌜v.val = List.replicate n.val x ∧ v.length = n.val⌝⦄ := by
  mvcgen [from_elem]
  sorry

/-
Original:
@[progress]
theorem alloc.vec.Vec.resize_spec {T} (cloneInst : core.clone.Clone T)
  (v : alloc.vec.Vec T) (new_len : Usize) (value : T)
  (hClone : cloneInst.clone value = ok value) :
  ∃ nv, alloc.vec.Vec.resize cloneInst v new_len value = ok nv ∧
    nv.val = v.val.resize new_len value := by
  rw [resize]
  split
  . simp
  . simp [*]
-/
@[spec]
theorem alloc.vec.Vec.resize_spec' {T} (cloneInst : core.clone.Clone T)
    (v : alloc.vec.Vec T) (new_len : Usize) (value : T)
    (hClone : cloneInst.clone value = ok value) :
    ⦃⌜True⌝⦄
    alloc.vec.Vec.resize cloneInst v new_len value
    ⦃⇓nv => ⌜nv.val = v.val.resize new_len value⌝⦄ := by
  rw [Vec.resize]
  split
  · mvcgen
  · mvcgen
    sorry

/-
Original:
@[progress]
theorem alloc.vec.FromBoxSliceVec.from_spec {T : Type} (v : alloc.vec.Vec T) :
  ∃ s, alloc.vec.FromBoxSliceVec.from v = ok s ∧ s.length = v.length ∧ s.val = v.val := by
  simp [alloc.vec.FromBoxSliceVec.from]
-/
@[spec]
theorem alloc.vec.FromBoxSliceVec.from_spec' {T : Type} (v : alloc.vec.Vec T) :
    ⦃⌜True⌝⦄
    alloc.vec.FromBoxSliceVec.from v
    ⦃⇓s => ⌜s.length = v.length ∧ s.val = v.val⌝⦄ := by
  mvcgen

end alloc.vec
end Aeneas.Std
