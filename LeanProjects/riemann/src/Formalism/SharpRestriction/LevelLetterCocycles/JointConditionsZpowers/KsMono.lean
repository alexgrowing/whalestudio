import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

section Up

variable {l : ℕ} [Fact l.Prime]

theorem Ks_mono (K : FinExt l) {s s' : ℕ} (h : s ≤ s') : Ks K s ≤ Ks K s' := by
  unfold Ks
  refine sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) _
  intro x hx
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have hx' : x ^ (l ^ s) = 1 := hx
  show x ^ (l ^ (s + k)) = 1
  rw [pow_add, pow_mul, hx', one_pow]

end Up

end Formalism.MainNotions.N
