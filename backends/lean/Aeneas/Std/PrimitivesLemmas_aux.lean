import Aeneas.Std.PrimitivesLemmas
import Aeneas.Mvcgen
import Std.Do
import Std.Tactic.Do

namespace Aeneas.Std

open Result Std.Do

/-
Original:
@[progress]
theorem massert_spec (b : Prop) [Decidable b] (h : b) :
  massert b = ok () := by
  simp [massert, *]
-/
@[spec]
theorem massert_spec' (b : Prop) [Decidable b] :
    ⦃⌜b⌝⦄
    massert b
    ⦃⇓_ => ⌜True⌝⦄ := by
  mvcgen [massert]
  -- To do (Oliver): complete proof
  sorry

end Aeneas.Std
