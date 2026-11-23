import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionZeroOneProperties
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedDiscGaugeCompletion_zero_one_properties : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ x y : Disc l (0 : Wq l bk.a) 1, ‖x * y‖ = ‖x‖ * ‖y‖) ∧ (∀ x : Disc l (0 : Wq l bk.a) 1, ‖x‖ ≤ 1 → ∃ w, x = toDisc l (0 : Wq l bk.a) 1 w) ∧ Function.Injective (toDisc l (0 : Wq l bk.a) 1) ∧ ∀ w : Wq l bk.a, IsUnit w → ‖toDisc l (0 : Wq l bk.a) 1 w‖ = 1 := by
  first | exact @GlobalTheory.BSP.disc_zero_one | exact GlobalTheory.BSP.disc_zero_one | (intros; apply GlobalTheory.BSP.disc_zero_one <;> assumption)
