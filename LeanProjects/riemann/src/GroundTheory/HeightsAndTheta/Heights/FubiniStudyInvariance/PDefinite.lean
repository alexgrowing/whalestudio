import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped LinearAlgebra.Projectivization ComplexConjugate Matrix ENNReal
open MeasureTheory Set MvPolynomial

noncomputable section

namespace FSInv

open CP

theorem Definite.proof (hPar : Parseval.Statement) (hI : InnerSelf.Statement) :
    Definite.Statement := by
  intro N n P hP
  constructor
  · intro h0
    have h1 : sectionL2NormSq (N := N) n P = 0 := by exact_mod_cast (hI N n P).symm.trans h0
    have h2 := hPar N n P hP
    rw [fubiniStudy_l2Norm_sq_eq, h1] at h2
    by_contra hne
    obtain ⟨a, ha⟩ : P.support.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (mt MvPolynomial.support_eq_empty.mp hne)
    have hpos : 0 < ∑ a ∈ P.support, ‖P.coeff a‖ ^ 2 *
        ((∏ i, ((a i).factorial : ℝ)) * N.factorial / (n + N).factorial) := by
      refine Finset.sum_pos' (fun b _ => by positivity) ⟨a, ha, ?_⟩
      have hc : P.coeff a ≠ 0 := MvPolynomial.mem_support_iff.mp ha
      have : 0 < ‖P.coeff a‖ := norm_pos_iff.mpr hc
      positivity
    linarith
  · rintro rfl
    rw [hI]
    simp [sectionL2NormSq, fsNormPoly]

end FSInv

end

end GroundTheory.Heights₂.Heights
