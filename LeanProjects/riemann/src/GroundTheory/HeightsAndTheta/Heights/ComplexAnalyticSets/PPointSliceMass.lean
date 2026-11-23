import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPointSliceMass
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PPointLine
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PPointChowForm
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PPointIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace PointSliceMass

variable {n : ℕ}

theorem isMultiHomog_pairing (y : Fin n → ℂ) :
    IsMultiHomog 1 (∑ j, C (y j) * X ((0 : Fin 1), j) : MvPolynomial (Fin 1 × Fin n) ℂ) := by
  unfold IsMultiHomog
  refine IsWeightedHomogeneous.sum _ _ _ fun j _ => ?_
  have hX := isWeightedHomogeneous_X (R := ℂ) (groupWeight 1 n) ((0 : Fin 1), j)
  have hw : groupWeight 1 n ((0 : Fin 1), j) = fun _ => 1 := by
    funext i
    rw [Fin.fin_one_eq_zero i]
    simp [groupWeight]
  rw [hw] at hX
  simpa using (isWeightedHomogeneous_C (groupWeight 1 n) (y j)).mul hX

theorem line_sup_eq_ker (y ℓ : Fin n → ℂ) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (hJ : ∀ q, q ∈ J ↔ ∀ t : ℂ, eval (t • y) q = 0) (hc0 : ∑ a, ℓ a * y a ≠ 0) :
    J ⊔ Ideal.span {linForm ℓ - 1} =
      RingHom.ker (MvPolynomial.eval ((∑ a, ℓ a * y a)⁻¹ • y)) := by
  set c := ∑ a, ℓ a * y a with hc
  set I := J ⊔ Ideal.span {linForm ℓ - 1} with hI
  have hsmul : ∀ t : ℂ, eval (t • y) (linForm ℓ) = t * c := by
    intro t
    simp only [hc, linForm, map_sum, map_mul, eval_C, eval_X, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  apply le_antisymm
  · refine sup_le (fun q hq => (hJ q).mp hq _) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one,
      hsmul, inv_mul_cancel₀ hc0, sub_self]
  · have hX : ∀ b, X b - C ((c⁻¹ • y) b) ∈ I := by
      intro b
      have h1 : ∀ a, C (y a) * X b - C (y b) * X a ∈ J := fun a => (hJ _).mpr fun t => by
        simp only [map_sub, map_mul, eval_C, eval_X, Pi.smul_apply, smul_eq_mul]
        ring
      have hs : ∑ a, C (ℓ a) * (C (y a) * X b - C (y b) * X a) =
          C c * X b - C (y b) * linForm ℓ := by
        rw [hc, map_sum, Finset.sum_mul, linForm, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [map_mul]
        ring
      have hcc : C c⁻¹ * C c = (1 : MvPolynomial (Fin n) ℂ) := by
        rw [← C_mul, inv_mul_cancel₀ hc0, C_1]
      have key : X b - C ((c⁻¹ • y) b) = C c⁻¹ * (∑ a, C (ℓ a) * (C (y a) * X b - C (y b) * X a) +
          C (y b) * (linForm ℓ - 1)) := by
        rw [hs, Pi.smul_apply, smul_eq_mul, C_mul]
        linear_combination (-X b) * hcc
      rw [key]
      exact Ideal.mul_mem_left _ _ (Ideal.add_mem _
        (Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (Ideal.mem_sup_left (h1 a)))
        (Ideal.mul_mem_left _ _ (Ideal.mem_sup_right (Ideal.subset_span rfl))))
    have hext : Ideal.Quotient.mkₐ ℂ I =
        (Algebra.ofId ℂ (MvPolynomial (Fin n) ℂ ⧸ I)).comp (aeval (c⁻¹ • y)) := by
      apply MvPolynomial.algHom_ext
      intro b
      rw [AlgHom.comp_apply, aeval_X, Algebra.ofId_apply, Ideal.Quotient.mkₐ_eq_mk,
        ← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq, MvPolynomial.algebraMap_eq]
      exact hX b
    intro q hq
    rw [RingHom.mem_ker] at hq
    have h := congrArg (fun φ => φ q) hext
    simp only [Ideal.Quotient.mkₐ_eq_mk, AlgHom.comp_apply, Algebra.ofId_apply] at h
    rw [← Ideal.Quotient.eq_zero_iff_mem, h]
    rw [show aeval (c⁻¹ • y) q = eval (c⁻¹ • y) q from rfl, hq, map_zero]

end PointSliceMass

open PointSliceMass in

theorem PointSliceMass.proof : PointSliceMass.Statement := by
  intro n δ h J f ℓ hJ hf hδ hℓ
  obtain ⟨y, hy0, hV, hline⟩ := PointLine.proof n J f hJ hf
  obtain ⟨c, hc0, hfc⟩ := PointChowForm.proof n J f y hf hy0 hV
  have hδ1 : δ = 1 := by
    have h1 : IsMultiHomog 1 f := by
      rw [hfc]
      unfold IsMultiHomog
      simpa using (isWeightedHomogeneous_C (groupWeight 1 n) c).mul (isMultiHomog_pairing y)
    exact congrFun (IsWeightedHomogeneous.inj_right hf.1 hδ h1) 0
  have hly : ∑ a, ℓ a * y a ≠ 0 := by
    intro h0
    apply hℓ
    rw [hline]
    intro t
    simp only [linForm, map_sum, map_mul, eval_C, eval_X, Pi.smul_apply, smul_eq_mul]
    rw [← mul_zero t, ← h0, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [line_sup_eq_ker y ℓ J hline hly, PointIntegral.proof, hδ1, Nat.cast_one]

end

end GroundTheory.Heights₂.Heights
