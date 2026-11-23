import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMixedSpaceReImCoordsTotallyComplex
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mixedSpace_reIm_coords_totallyComplex : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∃ e : mixedEmbedding.mixedSpace E ≃L[ℝ] ((InfinitePlace E → ℝ) × (InfinitePlace E → ℝ)), MeasurePreserving e volume volume ∧ ∀ x : E, e (mixedEmbedding E x) = (reV x, imV x) := by
  first | exact @GlobalTheory.SnMass.SkewVol.mixedSpace_reIm_coords | exact GlobalTheory.SnMass.SkewVol.mixedSpace_reIm_coords | (intros; apply GlobalTheory.SnMass.SkewVol.mixedSpace_reIm_coords <;> assumption)
