import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace RestCutLieFirst

theorem transport_smallPowerSum (f j k m : ℕ) (τ : Fin f) :
    restTransport f j k (j + k) (restFirstEquiv j k) (RestTerms.smallPowerSum f j k .first m τ) =
      (-1) ^ m * ∑ a : Fin j, (X (τ, Sum.inl a) : RootPoly f j k) ^ m := by
  rw [Finset.mul_sum]
  simp only [RestTerms.smallPowerSum, map_sum, map_pow]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hidx : (restFirstEquiv j k) (⟨a.val, by omega⟩ : Fin (j + k)) = Sum.inl a := by
    have : (⟨a.val, by omega⟩ : Fin (j + k)) = Fin.castAdd k a := rfl
    rw [this, restFirstEquiv, finSumFinEquiv_symm_apply_castAdd]
  simp only [RestTerms.yRoot, RestTerms.yIndex, RestTerms.SmallBlock.sign, restTransport,
    restRename, RingHom.comp_apply, map_mul, map_C, map_X, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, rename_X, rename_C, hidx]
  rw [mul_pow]
  congr 1
  simp

end RestCutLieFirst

theorem RestCutLieFirst.proof : RestCutLieFirst.Statement := by
  intro f j k _ m σ
  obtain ⟨τ, b⟩ := σ
  have hC1 : (C ((((-1 : ℚ) ^ m : ℚ) : ℝ)) : RootPoly f j k) = (-1) ^ m := by simp
  have hC2 : (C (((-1 : ℚ) : ℚ) : ℝ) : RootPoly f j k) = -1 := by simp
  have hC3 : (C ((-1 : ℝ) ^ m) : RootPoly f j k) = (-1) ^ m := by simp
  cases b with
  | false =>
    refine ⟨(-1) ^ m, 0, neg_one_pow_eq_or ℚ m, ?_⟩
    rw [RestCutLieFirst.transport_smallPowerSum, hC1]
    simp only [lieClass, map_zero, zero_mul, add_zero]
    rw [← mul_assoc, ← mul_pow]
    simp
  | true =>
    refine ⟨-1, (-1) ^ m, Or.inr rfl, ?_⟩
    rw [RestCutLieFirst.transport_smallPowerSum, hC2, hC3]
    simp only [lieClass, rootPsum, Fintype.sum_sum_type]
    ring

end

end GroundTheory.Heights₂.Heights
