import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormAinfDisc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gaussNorm_ainf_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∃ N : Ainf l → ℝ, (∀ x y, N (x * y) = N x * N y) ∧ (∀ x y, N (x + y) ≤ max (N x) (N y)) ∧ N (l : Ainf l) = (l : ℝ)⁻¹ ∧ (∀ x, N x ≤ ‖toDisc l (bk.ev X) ρ x‖) ∧ ∀ x, (ρ : ℝ) * ‖toDisc l (bk.ev X) ρ x‖ ≤ N x := by
  first | exact @GlobalTheory.DiscGauss.exists_gauss_disc | exact GlobalTheory.DiscGauss.exists_gauss_disc | (intros; apply GlobalTheory.DiscGauss.exists_gauss_disc <;> assumption)
