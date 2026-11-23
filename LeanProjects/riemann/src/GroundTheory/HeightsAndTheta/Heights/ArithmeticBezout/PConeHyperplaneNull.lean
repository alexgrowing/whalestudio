import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ConeBall
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsZeroLocusDimH
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowFormDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem ConeHyperplaneNull.proof (hZ : ZeroLocusDimH.Statement) (hC : ChowFormDimLe.Statement) :
    ConeHyperplaneNull.Statement := by
  intro n e h W f u hW hf hu
  have := hW.isPrime
  set J : Ideal (MvPolynomial (Fin n) ℂ) := W ⊔ Ideal.span {linForm u} with hJ

  have hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (e : ℕ) := by
    have h1 := hC ℂ n (e + 1) W f hW hf
    have hr : Ideal.Quotient.mk W (linForm u) ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ W) :=
      mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    have h2 := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor (le_sup_left : W ≤ J))
      (Ideal.Quotient.factor_surjective _) hr
      (by rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have h3 := h2.trans h1
    generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = a at h3 ⊢
    induction a using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe a =>
      induction a using ENat.recTopCoe with
      | top => exact absurd h3 (by norm_cast)
      | coe m =>
        have : m + 1 ≤ e + 1 := by exact_mod_cast h3
        exact_mod_cast (by omega : m ≤ e)

  let g : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n → ℂ) :=
    (Matrix.transpose h.mat).mulVecLin.comp (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap
  have hg : ∀ y, g y = h.pointOf y := fun _ => rfl
  have hinj : Function.Injective g := by
    have hu : IsUnit (Matrix.transpose h.mat) := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]; exact h.isUnit_det
    exact (Matrix.mulVec_injective_iff_isUnit.mpr hu).comp
      (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).injective
  obtain ⟨K, -, hK⟩ := (LinearMap.injective_iff_antilipschitz g).mp hinj

  have hsub : coneBall h W ∩ {y | ∑ j, u j * h.pointOf y j = 0} ⊆
      g ⁻¹' {x | ∀ q ∈ J, eval x q = 0} := by
    rintro y ⟨⟨-, hyW⟩, hyu⟩
    have hle : J ≤ RingHom.ker (eval (h.pointOf y)) := by
      refine sup_le (fun q hq => (RingHom.mem_ker).2 (hyW q hq)) ?_
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      simpa [linForm, map_sum] using hyu
    intro q hq
    rw [hg]
    exact (RingHom.mem_ker).1 (hle hq)
  have hdimH : dimH (coneBall h W ∩ {y | ∑ j, u j * h.pointOf y j = 0}) ≤ 2 * (e : ENNReal) :=
    (dimH_mono hsub).trans ((hK.dimH_preimage_le _).trans (hZ n e J hdim))
  have hlt : dimH (coneBall h W ∩ {y | ∑ j, u j * h.pointOf y j = 0}) <
      (((2 * (e + 1) : ℕ) : NNReal) : ENNReal) := by
    refine hdimH.trans_lt ?_
    rw [ENNReal.coe_natCast]
    exact_mod_cast (by omega : 2 * e < 2 * (e + 1))
  rw [show ((2 * (e + 1) : ℕ) : ℝ) = (((2 * (e + 1) : ℕ) : NNReal) : ℝ) from
    (NNReal.coe_natCast _).symm]
  exact hausdorffMeasure_of_dimH_lt hlt

end

end GroundTheory.Heights₂.Heights
