import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEisensteinMulClosedDiscEqRpow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_eisenstein_mul_closedDisc_eq_rpow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), bk.ρ₀ ≤ ρ → ρ < 1 → ∀ y : bk.DS ρ, ‖toDisc l (X : bk.S) ρ bk.E * y‖ = (ρ : ℝ) ^ bk.Ep.natDegree * ‖y‖ := by
  first | exact @GlobalTheory.BSP.BK.norm_toDisc_E_mul | exact GlobalTheory.BSP.BK.norm_toDisc_E_mul | (intros; apply GlobalTheory.BSP.BK.norm_toDisc_E_mul <;> assumption)
