import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinHomImageXDeltaZeroLiftsUniformizer
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinHom_image_X_delta_zero_lifts_uniformizer : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Obj l ↥(OL K)) (g : Hom bk.prism C), C.D.δ (BK.hf g X) = 0 ∧ Ideal.Quotient.mk C.I (BK.hf g X) = C.str (bk.str.symm (Ideal.Quotient.mk _ X)) := by
  first | exact @GlobalTheory.BSP.hf_X_δ_and_str | exact GlobalTheory.BSP.hf_X_δ_and_str | (intros; apply GlobalTheory.BSP.hf_X_δ_and_str <;> assumption)
