import Aeneas.Std.Array.ArraySlice
import Aeneas.Mvcgen
import Std.Do
import Std.Tactic.Do

namespace Aeneas.Std

open Result Error core.ops.range Std.Do

/-
Original:
@[progress]
theorem Array.subslice_spec {α : Type u} {n : Usize} [Inhabited α] (a : Array α n) (r : Range Usize)
  (h0 : r.start.val < r.end_.val) (h1 : r.end_.val ≤ a.val.length) :
  ∃ s, subslice a r = ok s ∧
  s.val = a.val.slice r.start.val r.end_.val ∧
  (∀ i, i + r.start.val < r.end_.val → s.val[i]! = a.val[r.start.val + i]!)
  := by
  simp only [subslice, true_and, h0, h1, ↓reduceIte, ok.injEq, exists_eq_left', true_and]
  intro i _
  have := List.getElem!_slice r.start.val r.end_.val i a.val (by scalar_tac)
  simp only [this]
-/
@[spec]
theorem Array.subslice_spec' {α : Type u} {n : Usize} [Inhabited α] (a : Array α n) (r : Range Usize)
    (h0 : r.start.val < r.end_.val) (h1 : r.end_.val ≤ a.val.length) :
    ⦃⌜True⌝⦄
    Array.subslice a r
    ⦃⇓s => ⌜s.val = a.val.slice r.start.val r.end_.val ∧
            (∀ i, i + r.start.val < r.end_.val → s.val[i]! = a.val[r.start.val + i]!)⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

/-
Original:
@[progress]
theorem Array.update_subslice_spec {α : Type u} {n : Usize} [Inhabited α] (a : Array α n) (r : Range Usize) (s : Slice α)
  (_ : r.start.val < r.end_.val) (_ : r.end_.val ≤ a.length) (_ : s.length = r.end_.val - r.start.val) :
  ∃ na, update_subslice a r s = ok na ∧
  (∀ i, i < r.start.val → na[i]! = a[i]!) ∧
  (∀ i, r.start.val ≤ i → i < r.end_.val → na[i]! = s[i - r.start.val]!) ∧
  (∀ i, r.end_.val ≤ i → i < n.val → na[i]! = a[i]!) := by
  simp [update_subslice]
  split <;> simp only [reduceCtorEq, false_and, exists_false, ok.injEq, exists_eq_left']
  . simp_lists
  . scalar_tac
-/
@[spec]
theorem Array.update_subslice_spec' {α : Type u} {n : Usize} [Inhabited α] (a : Array α n) (r : Range Usize) (s : Slice α)
    (h0 : r.start.val < r.end_.val) (h1 : r.end_.val ≤ a.length) (h2 : s.length = r.end_.val - r.start.val) :
    ⦃⌜True⌝⦄
    Array.update_subslice a r s
    ⦃⇓na => ⌜(∀ i, i < r.start.val → na[i]! = a[i]!) ∧
             (∀ i, r.start.val ≤ i → i < r.end_.val → na[i]! = s[i - r.start.val]!) ∧
             (∀ i, r.end_.val ≤ i → i < n.val → na[i]! = a[i]!)⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

end Aeneas.Std
