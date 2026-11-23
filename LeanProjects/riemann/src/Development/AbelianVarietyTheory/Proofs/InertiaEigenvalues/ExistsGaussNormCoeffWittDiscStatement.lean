import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormCoeffWittDisc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gaussNorm_coeff_wittDisc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∃ a : ℕ → (bk.DS ρ →+ Disc l (0 : Wq l bk.a) 1), (∀ n x, a n (toDisc l (X : bk.S) ρ x) = toDisc l (0 : Wq l bk.a) 1 (coeff n x)) ∧ (∀ n y, ‖a n y‖ * (ρ : ℝ) ^ n ≤ ‖y‖) ∧ (∀ y (r : ℝ), 0 ≤ r → (∀ n, ‖a n y‖ * (ρ : ℝ) ^ n ≤ r) → ‖y‖ ≤ r) ∧ ∀ y, Filter.Tendsto (fun n => ‖a n y‖ * (ρ : ℝ) ^ n) Filter.atTop (nhds 0) := by
  first | exact @GlobalTheory.BSP.DiscSer.exists_coeff_disc | exact GlobalTheory.BSP.DiscSer.exists_coeff_disc | (intros; apply GlobalTheory.BSP.DiscSer.exists_coeff_disc <;> assumption)
