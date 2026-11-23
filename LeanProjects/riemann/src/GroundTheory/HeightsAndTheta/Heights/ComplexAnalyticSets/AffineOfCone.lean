import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.RingKrullDimQuotBotOne
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.FrameProjEq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

noncomputable section

theorem SlabBound.affine : GroundTheory.Heights₂.Heights.SlabBound.Statement := by
  intro n d J A u hJ hA hu
  classical
  set φ : MvPolynomial (Fin d) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ J :=
    (GroundTheory.Heights₂.Heights.linProjHom J A : MvPolynomial (Fin d) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ J)
    with hφ
  set v : MvPolynomial (Fin n) ℂ ⧸ J := Ideal.Quotient.mk J (GroundTheory.Heights₂.Heights.linForm u) with hv
  have hv0 : v ≠ 0 := by
    rw [hv, Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hu
  obtain ⟨p, hpm, hp⟩ := hA.finite.to_isIntegral v
  obtain ⟨q, hpq, hq⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hpm.ne_zero 0
  have hq0 : q.coeff 0 ≠ 0 := by
    intro h
    apply hq
    rw [map_zero, sub_zero]
    exact Polynomial.X_dvd_iff.mpr h
  have hqv : q.eval₂ φ v = 0 := by
    rw [hpq, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_sub, Polynomial.eval₂_X,
      Polynomial.eval₂_C, map_zero, sub_zero] at hp
    exact (mul_eq_zero.mp hp).resolve_left (pow_ne_zero _ hv0)
  refine ⟨q.coeff 0, hq0, fun R => ?_⟩
  let g : EuclideanSpace ℂ (Fin n) → ℂ := fun z =>
    ∑ i ∈ Finset.range (q.divX.natDegree + 1),
      eval (A.mulVec fun j => z j) (q.divX.coeff i) * (∑ j, u j * z j) ^ i
  have hg : Continuous g := by
    refine continuous_finsetSum _ fun i _ => ?_
    refine Continuous.mul ?_ ?_
    · exact (MvPolynomial.continuous_eval _).comp (by fun_prop)
    · fun_prop
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : EuclideanSpace ℂ (Fin n)) R).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨K, fun z hz hzR => ?_⟩
  let ev : MvPolynomial (Fin n) ℂ ⧸ J →+* ℂ :=
    Ideal.Quotient.lift J (eval fun j => z j) (fun a ha => hz a ha)
  have hevφ : ev.comp φ = eval (A.mulVec fun j => z j) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [ev, φ, GroundTheory.Heights₂.Heights.linProjHom]
    · intro i
      simp [ev, φ, GroundTheory.Heights₂.Heights.linProjHom, Matrix.mulVec, dotProduct]
  have hevv : ev v = ∑ j, u j * z j := by
    simp [ev, v, GroundTheory.Heights₂.Heights.linForm]
  have key : q.eval₂ (eval (A.mulVec fun j => z j)) (∑ j, u j * z j) = 0 := by
    have h1 := congrArg ev hqv
    rw [Polynomial.hom_eval₂, hevφ, hevv, map_zero] at h1
    exact h1
  have hsplit : eval (A.mulVec fun j => z j) (q.coeff 0) = -((∑ j, u j * z j) * g z) := by
    have h2 := congrArg (fun r => r.eval₂ (eval (A.mulVec fun j => z j)) (∑ j, u j * z j))
      (Polynomial.X_mul_divX_add q)
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C,
      key] at h2
    rw [Polynomial.eval₂_eq_sum_range] at h2
    linear_combination h2
  have hzb : z ∈ Metric.closedBall (0 : EuclideanSpace ℂ (Fin n)) R := mem_closedBall_zero_iff.mpr hzR
  rw [hsplit, norm_neg, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hK z hzb) (norm_nonneg _)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
