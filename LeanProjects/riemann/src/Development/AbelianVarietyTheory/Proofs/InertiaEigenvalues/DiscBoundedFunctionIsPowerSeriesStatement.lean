import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscBoundedFunctionIsPowerSeries
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.disc_bounded_function_isPowerSeries : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ y : bk.DS ρ, (∀ ρ₁ : ℝ≥0, ρ₁ < 1 → ∃ (ρ' : ℝ≥0) (R : bk.DS ρ' →+* bk.DS ρ) (y' : bk.DS ρ'), ρ₁ ≤ ρ' ∧ ρ ≤ ρ' ∧ ρ' < 1 ∧ IsDiscMap (RingHom.id bk.S) R ∧ R y' = y ∧ ‖y'‖ ≤ 1) → ∃ a, toDisc l (X : bk.S) ρ a = y := by
  first | exact @GlobalTheory.BSP.disc_bdd_isSeries | exact GlobalTheory.BSP.disc_bdd_isSeries | (intros; apply GlobalTheory.BSP.disc_bdd_isSeries <;> assumption)
