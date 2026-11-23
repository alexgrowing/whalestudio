import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasEuclideanBallVolumeHaarComplexGLInverse
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasEuclideanBallVolume_haarComplexGL_inverse : ∀ j : ℕ, IsRadial (ENNReal.ofReal (2 ^ (j ^ 2)) • haarLoc j) (fun x => Formalism.REAL.hs (Matrix.of x - 1) + Formalism.REAL.hs ((Matrix.of x)⁻¹ - 1)) (2 * j ^ 2) := by
  first | exact @GlobalTheory.LeviIso.isRadial_haarLoc | exact GlobalTheory.LeviIso.isRadial_haarLoc | (intros; apply GlobalTheory.LeviIso.isRadial_haarLoc <;> assumption)
