import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralPolynomialTorsionCharacterLevel
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_polynomial_torsion_character_level : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (p : ℕ) [Fact p.Prime] (F : FormalGroup K), Intg F.toPowerSeries → ∀ t : ℕ → K, (∀ n, ‖t n‖ < 1) → t 0 = 0 → t 1 ≠ 0 → (∀ n, ev1 (nMul F p) (t (n + 1)) = t n) → ∀ (n : ℕ) (ζ : K), ζ ^ (p ^ n) = 1 → ∃ g : Polynomial K, (∀ k, ‖g.coeff k‖ ≤ 1) ∧ ∀ j : ℕ, g.eval (ev1 (nMul F j) (t n)) = ζ ^ j := by
  first | exact @GlobalTheory.ConvSer.exists_intg_polynomial_level | exact GlobalTheory.ConvSer.exists_intg_polynomial_level | (intros; apply GlobalTheory.ConvSer.exists_intg_polynomial_level <;> assumption)
