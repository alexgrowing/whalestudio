import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModRepsCardLe
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
open NumberField ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reps_mod_lattice_card_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (Λ : Submodule (𝓞 E) (Fin r → E)), 1 ≤ M → Λ.FG → ∃ T : Finset (Fin r → E), T.card ≤ M ^ (2 * fdeg E * r) ∧ (∀ t ∈ T, t ∈ Λ) ∧ ∀ x ∈ Λ, ∃ t ∈ T, ∃ y ∈ Λ, x = t + M • y := by
  first | exact @GlobalTheory.lattice_mod_reps_card_le | exact GlobalTheory.lattice_mod_reps_card_le | (intros; apply GlobalTheory.lattice_mod_reps_card_le <;> assumption)
