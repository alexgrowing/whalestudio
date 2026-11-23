import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelProper
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

theorem isRoot_map_eval_of_mem_zeroSetIn {n m : ℕ} {I : Ideal (MvPolynomial (Fin n ⊕ Fin m) ℂ)}
    {w : Fin n ⊕ Fin m → ℂ} (hw : w ∈ zeroSetIn I) (i : Fin m) (P : Polynomial (MvPolynomial (Fin n) ℂ))
    (hP : P.eval₂ (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin m) ℂ).toRingHom
      (X (Sum.inr i)) ∈ I) :
    (P.map (eval (firstCoords w))).IsRoot (w (Sum.inr i)) := by
  have h0 := hw _ hP
  rw [Polynomial.hom_eval₂, eval_X] at h0
  have hcomp : (eval w).comp
      (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin m) ℂ).toRingHom =
      eval (firstCoords w) := by
    ext q
    · simp
    · simp [firstCoords]
  rw [hcomp, Polynomial.eval₂_eq_eval_map] at h0
  exact h0

theorem norm_lt_of_isRoot_map_eval {n : ℕ} {P : Polynomial (MvPolynomial (Fin n) ℂ)} (hPm : P.Monic)
    (x : Fin n → ℂ) {a : ℂ} (ha : (P.map (eval x)).IsRoot a) :
    ‖a‖ < 1 + ∑ j ∈ Finset.range P.natDegree, ‖eval x (P.coeff j)‖ := by
  have hQm : (P.map (eval x)).Monic := hPm.map _
  have hlt := Polynomial.IsRoot.norm_lt_cauchyBound hQm.ne_zero ha
  have hcb : Polynomial.cauchyBound (P.map (eval x)) ≤
      (∑ j ∈ Finset.range P.natDegree, ‖eval x (P.coeff j)‖₊) + 1 := by
    rw [Polynomial.cauchyBound, hQm.leadingCoeff, nnnorm_one, div_one, hPm.natDegree_map]
    gcongr
    refine Finset.sup_le fun j hj => ?_
    rw [Polynomial.coeff_map]
    exact Finset.single_le_sum (f := fun j => ‖eval x (P.coeff j)‖₊) (fun _ _ => zero_le) hj
  have h := hlt.trans_le hcb
  rw [← NNReal.coe_lt_coe, NNReal.coe_add, NNReal.coe_sum, coe_nnnorm, NNReal.coe_one] at h
  simp only [coe_nnnorm] at h
  linarith

theorem NormalModelProper.proof : NormalModelProper.Statement := by
  intro n J M K hK
  choose P hPm hP using M.integral
  set f : (Fin n → ℂ) → ℝ := fun x =>
    ∑ i, ∑ j ∈ Finset.range (P i).natDegree, ‖eval x ((P i).coeff j)‖ with hf
  have hfc : Continuous f := by
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact (MvPolynomial.continuous_eval _).norm
  obtain ⟨C, hC⟩ := hK.isCompact_closure.exists_bound_of_continuousOn hfc.continuousOn
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hK
  refine isBounded_iff_forall_norm_le.2 ⟨max R (1 + C), fun w hw => ?_⟩
  obtain ⟨hwZ, hwK⟩ := hw
  have hxR : ‖firstCoords w‖ ≤ R := hR _ hwK
  have hR0 : 0 ≤ max R (1 + C) := (norm_nonneg _).trans (hxR.trans (le_max_left _ _))
  refine (pi_norm_le_iff_of_nonneg hR0).2 fun s => ?_
  rcases s with j | i
  · exact ((norm_le_pi_norm (firstCoords w) j).trans hxR).trans (le_max_left _ _)
  · have hroot := isRoot_map_eval_of_mem_zeroSetIn hwZ i (P i) (hP i)
    have hlt := norm_lt_of_isRoot_map_eval (hPm i) (firstCoords w) hroot
    have hfi : ∑ j ∈ Finset.range (P i).natDegree, ‖eval (firstCoords w) ((P i).coeff j)‖ ≤
        f (firstCoords w) :=
      Finset.single_le_sum (f := fun i => ∑ j ∈ Finset.range (P i).natDegree,
        ‖eval (firstCoords w) ((P i).coeff j)‖) (fun i _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.mem_univ i)
    have hfC : f (firstCoords w) ≤ C := by
      have := hC _ (subset_closure hwK)
      exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)
    exact (hlt.le.trans (by linarith)).trans (le_max_right _ _)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
