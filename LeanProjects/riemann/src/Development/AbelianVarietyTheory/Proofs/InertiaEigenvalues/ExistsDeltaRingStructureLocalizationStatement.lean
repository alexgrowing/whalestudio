import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeltaRingStructureLocalization
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deltaRingStructure_localization : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (M : Submonoid A), (∀ x ∈ M, D.φ x ∈ M) → ∃ D' : Delta l (Localization M), IsδMap D D' (algebraMap A (Localization M)) := by
  first | exact @GlobalTheory.BSP.delta_localization | exact GlobalTheory.BSP.delta_localization | (intros; apply GlobalTheory.BSP.delta_localization <;> assumption)
