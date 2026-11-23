import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearPDivGroupHomChartConstantCoeffSubst
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinearPDivGroupHom_chart_constantCoeff_subst : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (φ : Fin d → MvPowerSeries (Fin e) k'), (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → (∀ j, constantCoeff (φ j) = 0) ∧ ∀ n g, c'.ev n (subst φ (MvPowerSeries.map σ g)) = s.app n (c.ev n g) := by
  first | exact @GlobalTheory.Katz.semiHom_constantCoeff_and_ev | exact GlobalTheory.Katz.semiHom_constantCoeff_and_ev | (intros; apply GlobalTheory.Katz.semiHom_constantCoeff_and_ev <;> assumption)
