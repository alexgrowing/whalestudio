import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped LinearAlgebra.Projectivization ComplexConjugate Matrix ENNReal
open MeasureTheory Set MvPolynomial

noncomputable section

namespace FSInv

open CP

theorem InnerSelf.proof : InnerSelf.Statement := by
  intro N n P
  rw [l2Inner, sectionL2NormSq, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [fsPair, fsNormPoly]
  have hn : ((norm2 x.rep : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (euclideanNorm_pos x.rep_nonzero).ne'
  rw [mul_comm (conj _), Complex.mul_conj']
  push_cast
  field_simp
  ring

end FSInv

end

end GroundTheory.Heights₂.Heights
