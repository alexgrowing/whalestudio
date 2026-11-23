import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace RestCutCompareReal

theorem realFlagIntegral_monomial (f N : ℕ) (α : Fin f × Fin N →₀ ℕ) (r : ℝ) :
    realFlagIntegral f N (monomial α r) =
      r * (RestTerms.flagIntegral f N (monomial α (1 : ℚ)) : ℝ) := by
  unfold realFlagIntegral RestTerms.flagIntegral
  rw [Rat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [coeff_monomial, coeff_monomial]
  split_ifs <;> push_cast <;> ring

theorem realFlagIntegral_eq_sum (f N : ℕ) (P : MvPolynomial (Fin f × Fin N) ℝ) :
    realFlagIntegral f N P =
      ∑ α ∈ P.support, realFlagIntegral f N (monomial α (coeff α P)) := by
  unfold realFlagIntegral
  conv_lhs => rw [P.as_sum]
  simp only [coeff_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem restRename_monomial (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k)
    (α : Fin f × Fin N →₀ ℕ) (r : ℝ) :
    restRename f j k N e (monomial α r) = r • restTransport f j k N e (monomial α (1 : ℚ)) := by
  have h : (monomial α r : MvPolynomial (Fin f × Fin N) ℝ) =
      r • map (algebraMap ℚ ℝ) (monomial α (1 : ℚ)) := by
    rw [map_monomial, smul_monomial, map_one, smul_eq_mul, mul_one]
  rw [h, map_smul]
  rfl

end RestCutCompareReal

open RestCutCompareReal in

theorem RestCutCompareReal.proof : RestCutCompareReal.Statement := by
  intro f j k N e I c d hI P hP
  have hmono : ∀ α ∈ P.support, I (restRename f j k N e (monomial α (coeff α P))) =
      c * realFlagIntegral f N (monomial α (coeff α P)) := by
    intro α hα
    have hdeg : (monomial α (1 : ℚ) : RestTerms.RootRing f N).IsHomogeneous d :=
      isHomogeneous_monomial 1 (by
        by_contra h
        exact mem_support_iff.mp hα (hP.coeff_eq_zero h))
    rw [restRename_monomial, map_smul, hI _ hdeg, realFlagIntegral_monomial, smul_eq_mul]
    ring
  have hL : I (restRename f j k N e P) =
      ∑ α ∈ P.support, I (restRename f j k N e (monomial α (coeff α P))) := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum, map_sum]
  rw [hL, realFlagIntegral_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl hmono

end

end GroundTheory.Heights₂.Heights
