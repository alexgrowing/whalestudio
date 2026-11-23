import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCuspidalMultisetsTotalDegreeLe
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters
open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_cuspidal_multisets_total_degree_le : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ), 0 < n → ∀ S : Finset (Multiset (Pc g)), (∀ M ∈ S, (M.map fun p => p.1).sum = n ∧ ∀ p ∈ M, IsCusp p.2) → S.card ≤ g ^ n - g ^ (n - 1) := by
  first | exact @GlobalTheory.GLq.CuspMultisetCount.card_le | exact GlobalTheory.GLq.CuspMultisetCount.card_le | (intros; apply GlobalTheory.GLq.CuspMultisetCount.card_le <;> assumption)
