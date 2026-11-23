import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsUnimodularBesselModelUnitaryGroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnimodular_besselModelUnitaryGroup : ∀ (k r : ℕ) (μ : Measure (Mt k r)), IsHaarOn (GG k r) μ → IsUnimod (GG k r) μ := by
  first | exact @GlobalTheory.SgInf.isUnimod_GG | exact GlobalTheory.SgInf.isUnimod_GG | (intros; apply GlobalTheory.SgInf.isUnimod_GG <;> assumption)
