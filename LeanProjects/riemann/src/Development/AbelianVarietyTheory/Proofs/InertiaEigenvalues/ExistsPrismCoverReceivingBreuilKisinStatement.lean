import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrismCoverReceivingBreuilKisin
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prism_cover_receiving_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)), ∃ (C : Obj l ↥(OL K)) (h : Hom B C), Nonempty (Hom bk.prism C) ∧ Cover h := by
  first | exact @GlobalTheory.BSP.exists_cover_receiving_bk | exact GlobalTheory.BSP.exists_cover_receiving_bk | (intros; apply GlobalTheory.BSP.exists_cover_receiving_bk <;> assumption)
