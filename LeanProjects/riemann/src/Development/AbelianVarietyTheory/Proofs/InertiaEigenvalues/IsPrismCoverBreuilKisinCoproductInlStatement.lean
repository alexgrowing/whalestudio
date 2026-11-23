import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPrismCoverBreuilKisinCoproductInl
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPrismCover_breuilKisinCoproduct_inl : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (t p : B.A), IsFrame bk B t p → ∀ En : Env bk B t p, Cover En.inl := by
  first | exact @GlobalTheory.BSP.env_inl_cover | exact GlobalTheory.BSP.env_inl_cover | (intros; apply GlobalTheory.BSP.env_inl_cover <;> assumption)
