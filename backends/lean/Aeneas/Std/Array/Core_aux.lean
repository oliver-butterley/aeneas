import Aeneas.Std.Array.Core
import Aeneas.Mvcgen
import Std.Do
import Std.Tactic.Do

namespace Aeneas.Std

open Result Std.Do

/-
Original:
@[progress]
def List.clone_spec {clone : α → Result α} {l : List α} (h : ∀ x ∈ l, clone x = ok x) :
  ∃ l', List.clone clone l = ok l' ∧ l'.val = l ∧ l'.val.length = l.length := by
  simp only [List.clone]
  have := List.mapM_clone_eq h
  split <;> simp_all
-/
@[spec]
theorem List.clone_spec' {clone : α → Result α} {l : List α} (h : ∀ x ∈ l, clone x = ok x) :
    ⦃⌜True⌝⦄
    List.clone clone l
    ⦃⇓l' => ⌜l'.val = l ∧ l'.val.length = l.length⌝⦄ := by
  -- To do (Oliver): complete proof
  sorry

end Aeneas.Std
