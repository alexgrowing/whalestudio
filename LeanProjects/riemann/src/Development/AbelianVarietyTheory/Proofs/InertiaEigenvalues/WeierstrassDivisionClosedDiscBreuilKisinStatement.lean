import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeierstrassDivisionClosedDiscBreuilKisin
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrass_division_closedDisc_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), bk.ρ₀ ≤ ρ → ρ < 1 → ∀ y : bk.DS ρ, ∃ (q : bk.DS ρ) (k : ℕ) (r : Polynomial (Wq l bk.a)), r.degree < bk.Ep.degree ∧ ((l : ℕ) : bk.DS ρ) ^ k * y = toDisc l (X : bk.S) ρ bk.E * q + toDisc l (X : bk.S) ρ (r : bk.S) := by
  first | exact @GlobalTheory.BSP.WDiv.weierstrass_div | exact GlobalTheory.BSP.WDiv.weierstrass_div | (intros; apply GlobalTheory.BSP.WDiv.weierstrass_div <;> assumption)
