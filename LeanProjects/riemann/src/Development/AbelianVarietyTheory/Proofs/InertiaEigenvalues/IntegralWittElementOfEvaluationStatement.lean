import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralWittElementOfEvaluation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_witt_element_of_evaluation : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∀ w ∈ bk.OE, ∀ a : Ainf l, w = inclW l a → ∃ s : bk.S, a = bk.ev s := by
  first | exact @GlobalTheory.BSP.ainf_inter_OE | exact GlobalTheory.BSP.ainf_inter_OE | (intros; apply GlobalTheory.BSP.ainf_inter_OE <;> assumption)
