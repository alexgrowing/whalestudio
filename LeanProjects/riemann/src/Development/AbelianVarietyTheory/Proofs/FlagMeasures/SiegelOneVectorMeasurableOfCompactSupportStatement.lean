import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelOneVectorMeasurableOfCompactSupport
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SiegelMeanCc
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_one_vector_measurable_of_compactSupport : GlobalTheory.GaussMean.OneVectorCc → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → SW1b2 F E σ M J := by
  first | exact @GlobalTheory.OneVecMeas.sw1b2_of_cc | exact GlobalTheory.OneVecMeas.sw1b2_of_cc | (intros; apply GlobalTheory.OneVecMeas.sw1b2_of_cc <;> assumption)
