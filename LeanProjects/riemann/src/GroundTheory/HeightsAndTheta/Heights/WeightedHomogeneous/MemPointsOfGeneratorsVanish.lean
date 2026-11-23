import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open scoped ContDiff

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [DecidableEq ι] in

theorem contDiff_evalCone (f : MvPolynomial (Coord n) ℤ) :
    ContDiff ℝ ∞ (fun z : Cone n ℂ ↦ evalCone z f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simpa only [evalCone, eval₂_C] using contDiff_const
  | add p q hp hq => simpa only [evalCone, eval₂_add] using hp.add hq
  | mul_X p v hp =>
    simpa only [evalCone, eval₂_mul, eval₂_X] using
      hp.mul (contDiff_pi.1 (contDiff_pi.1 contDiff_id v.1) v.2)

theorem ContDiffOn.zpow_of_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {s : Set E} (hf : ContDiffOn ℝ ∞ f s) (h0 : ∀ x ∈ s, f x ≠ 0) (m : ℤ) :
    ContDiffOn ℝ ∞ (fun x ↦ f x ^ m) s := by
  cases m with
  | ofNat k => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hf.pow k
  | negSucc k =>
    simp only [zpow_negSucc]
    exact (hf.pow (k + 1)).inv fun x hx ↦ pow_ne_zero _ (h0 x hx)

omit [Fintype ι] in

theorem ArithVariety.mem_points_of_generators_vanish (P : ArithVariety n) {r : ℕ}
    {G : Fin r → MvPolynomial (Coord n) ℤ} {δ : Fin r → ι → ℕ} (hG : P.IsHomogGenerators G δ)
    {z : Cone n ℂ} (hz : BlockNonzero z) (h0 : ∀ i, evalCone z (G i) = 0) : z ∈ P.points ℂ := by
  refine ⟨hz, fun f hf ↦ ?_⟩
  rw [← hG.span_eq] at hf
  have hle : Ideal.span (Set.range G) ≤
      RingHom.ker (eval₂Hom (Int.castRingHom ℂ) fun v : Coord n ↦ z v.1 v.2) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact h0 i
  exact hle hf

theorem ChartDenominatorAlt.proof (hV : ChartVanishing.Statement) : ChartDenominatorAlt.Statement := by
  intro ι _ _ n P D d g hg r G δ hG
  refine ⟨fun z hz ↦ ?_, ?_⟩
  · have hB : 0 ≤ ∑ i, ‖evalCone z (G i)‖ ^ 2 *
        ∏ k, l2Norm (z k) ^ (2 * ((d k : ℤ) + D.deg k - δ i k)) :=
      Finset.sum_nonneg fun i _ ↦ mul_nonneg (sq_nonneg _)
        (Finset.prod_nonneg fun k _ ↦ zpow_nonneg (Real.sqrt_nonneg _) _)
    have hA : 0 ≤ ∑ c, ∑ j, ‖evalCone z (g c j)‖ ^ 2 :=
      Finset.sum_nonneg fun c _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg _
    unfold AddBlockData.den
    by_cases hGz : ∃ i, evalCone z (G i) ≠ 0
    · obtain ⟨i, hi⟩ := hGz
      refine add_pos_of_nonneg_of_pos hA (Finset.sum_pos' (fun i _ ↦ ?_) ⟨i, Finset.mem_univ i, ?_⟩)
      · exact mul_nonneg (sq_nonneg _)
          (Finset.prod_nonneg fun k _ ↦ zpow_nonneg (Real.sqrt_nonneg _) _)
      · exact mul_pos (pow_pos (norm_pos_iff.mpr hi) 2)
          (Finset.prod_pos fun k _ ↦ zpow_pos (vectorL2Norm_pos (hz k)) _)
    · push Not at hGz
      have hzP := P.mem_points_of_generators_vanish hG hz hGz
      have hc : ∀ k, ∃ i, z k i ≠ 0 := fun k ↦ Function.ne_iff.mp (hz k)
      choose c hc using hc
      have hm : evalCone z (chartMonomial c d) ≠ 0 := by
        rw [evalCone_chartMonomial]
        exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)
      have hj : ∃ j, evalCone z (g c j) ≠ 0 := by
        by_contra hne
        push Not at hne
        exact hm ((hV ι n P D d g hg z hzP c).mp hne)
      obtain ⟨j, hj⟩ := hj
      refine add_pos_of_pos_of_nonneg (Finset.sum_pos' (fun c _ ↦ ?_) ⟨c, Finset.mem_univ c, ?_⟩) hB
      · exact Finset.sum_nonneg fun j _ ↦ sq_nonneg _
      · exact Finset.sum_pos' (fun j _ ↦ sq_nonneg _)
          ⟨j, Finset.mem_univ j, pow_pos (norm_pos_iff.mpr hj) 2⟩
  · have hsq : ∀ f : MvPolynomial (Coord n) ℤ,
        ContDiff ℝ ∞ (fun z : Cone n ℂ ↦ ‖evalCone z f‖ ^ 2) :=
      fun f ↦ (contDiff_norm_sq ℝ).comp (contDiff_evalCone f)
    unfold AddBlockData.den
    refine ContDiffOn.add ?_ ?_
    · exact (ContDiff.sum fun c _ ↦ ContDiff.sum fun j _ ↦ hsq (g c j)).contDiffOn
    · refine ContDiffOn.sum fun i _ ↦ (hsq (G i)).contDiffOn.mul ?_
      refine contDiffOn_prod fun k _ ↦ ?_
      exact ContDiffOn.zpow_of_ne_zero (contDiffOn_l2Norm_block k)
        (fun z hz ↦ (vectorL2Norm_pos (hz k)).ne') _

end

end GroundTheory.Heights₂.Heights
