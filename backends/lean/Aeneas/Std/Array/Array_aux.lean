import Aeneas.Std.Array.Array
import Aeneas.Mvcgen
import Std.Do
import Std.Tactic.Do

namespace Aeneas.Std

open Result Error Std.Do

/-
Original:
@[progress]
theorem Array.repeat_spec {α : Type u} (n : Usize) (x : α) :
  ∃ a, Array.repeat n x = a ∧ a.val = List.replicate n.val x := by
  simp [Array.repeat]
-/
-- To do (Oliver): doesn't fit the standard pattern for `spec` (pure function)

/-
Original:
@[progress]
theorem Array.index_usize_spec {α : Type u} {n : Usize} [Inhabited α] (v: Array α n) (i: Usize)
  (hbound : i.val < v.length) :
  ∃ x, v.index_usize i = ok x ∧ x = v.val[i.val]! := by
  simp only [index_usize]
  simp at *
  split <;> simp_all only [List.Vector.length_val, List.getElem?_eq_getElem, Option.some.injEq,
    Option.getD_some, reduceCtorEq]
-/
@[spec]
theorem Array.index_usize_spec' {α : Type u} {n : Usize} [Inhabited α] (v : Array α n) (i : Usize)
    (hbound : i.val < v.length) :
    ⦃⌜True⌝⦄
    v.index_usize i
    ⦃⇓x => ⌜x = v.val[i.val]!⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

/-
Original:
@[progress]
theorem Array.update_spec {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x : α)
  (hbound : i.val < v.length) :
  ∃ nv, v.update i x = ok nv ∧
  nv = v.set i x
  := by
  simp only [update, set]
  simp at *
  split <;> simp_all
-/
@[spec]
theorem Array.update_spec' {α : Type u} {n : Usize} (v : Array α n) (i : Usize) (x : α)
    (hbound : i.val < v.length) :
    ⦃⌜True⌝⦄
    v.update i x
    ⦃⇓nv => ⌜nv = v.set i x⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

/-
Original:
@[progress]
theorem Array.index_mut_usize_spec {α : Type u} {n : Usize} [Inhabited α] (v: Array α n) (i: Usize)
  (hbound : i.val < v.length) :
  ∃ x, v.index_mut_usize i = ok (x, set v i) ∧
  x = v.val[i.val]! := by
  simp only [index_mut_usize, Bind.bind, bind]
  have ⟨ x, h ⟩ := index_usize_spec v i hbound
  simp [h]
-/
@[spec]
theorem Array.index_mut_usize_spec' {α : Type u} {n : Usize} [Inhabited α] (v : Array α n) (i : Usize)
    (hbound : i.val < v.length) :
    ⦃⌜True⌝⦄
    v.index_mut_usize i
    ⦃⇓r => ⌜r = (v.val[i.val]!, Array.set v i)⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

/-
Original:
@[progress]
theorem Array.clone_spec {α : Type u} {n : Usize} {clone : α → Result α} {s : Array α n} (h : ∀ x ∈ s.val, clone x = ok x) :
  Array.clone clone s = ok s := by
  simp only [Array.clone]
  have ⟨ l', h ⟩ := List.clone_spec h
  simp [h]
-/
-- To do (Oliver): doesn't fit the standard pattern for `spec` (no existential result)

/-
Original:
@[progress]
theorem core.array.CloneArray.clone_spec {T : Type} {N : Usize} (cloneInst : core.clone.Clone T) (a : Array T N)
  (h : ∀ x ∈ a.val, cloneInst.clone x = ok x) :
  core.array.CloneArray.clone cloneInst a = ok a := by
  unfold clone
  rw [Array.clone_spec h]
-/
-- To do (Oliver): doesn't fit the standard pattern for `spec` (no existential result)

/-
Original:
@[progress]
theorem core.array.CloneArray.clone_from_spec {T : Type} {N : Usize} (cloneInst : core.clone.Clone T)
  (self source : Array T N) (h : ∀ x ∈ source.val, cloneInst.clone x = ok x) :
  core.array.CloneArray.clone_from cloneInst self source = ok source := by
  unfold clone_from
  rw [Array.clone_spec h]
-/
-- To do (Oliver): doesn't fit the standard pattern for `spec` (no existential result)

end Aeneas.Std
