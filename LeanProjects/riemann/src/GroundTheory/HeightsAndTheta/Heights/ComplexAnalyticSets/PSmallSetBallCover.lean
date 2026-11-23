import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSmallSetBallCover
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSmallSetTubeVolume
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets Metric

noncomputable section

theorem volume_ball_pi_complex {n : ℕ} (c : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    volume (ball c ρ) = ENNReal.ofReal ((Real.pi * ρ ^ 2) ^ n) := by
  rw [ball_pi c hρ, volume_pi_pi]
  simp only [Complex.volume_ball, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hρ.le,
    mul_comm, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]

theorem exists_cover_le_volume_thickening {n : ℕ} {A : Set (Fin n → ℂ)} (hA : IsCompact A) {r : ℝ}
    (hr : 0 < r) : ∃ T : Finset (Fin n → ℂ), (↑T : Set (Fin n → ℂ)) ⊆ A ∧ A ⊆ ⋃ c ∈ T, ball c r ∧
      (T.card : ℝ) * (Real.pi * (r / 4) ^ 2) ^ n ≤ (volume (thickening r A)).toReal := by
  set δ : NNReal := ⟨r / 4, by positivity⟩
  have hδ : (δ : ℝ) = r / 4 := rfl
  have hpack : packingNumber (2 * δ) A ≠ ⊤ := by
    obtain ⟨N, -, hNfin, hN⟩ := exists_finite_isCover_of_isCompact (ε := δ)
      (by rw [ne_eq, ← NNReal.coe_eq_zero, hδ]; positivity) hA
    exact ne_top_of_le_ne_top (Set.encard_ne_top_iff.2 hNfin)
      ((packingNumber_two_mul_le_externalCoveringNumber δ A).trans hN.externalCoveringNumber_le_encard)
  set S := maximalSeparatedSet (2 * δ) A
  have hSfin : S.Finite := Set.encard_ne_top_iff.1 (by rw [encard_maximalSeparatedSet hpack]; exact hpack)
  refine ⟨hSfin.toFinset, by simpa using maximalSeparatedSet_subset, ?_, ?_⟩
  · refine ((isCover_maximalSeparatedSet hpack).subset_iUnion_closedBall).trans ?_
    refine Set.iUnion₂_subset fun c hc => ?_
    refine (closedBall_subset_ball ?_).trans (Set.subset_biUnion_of_mem (u := fun c => ball c r) ?_)
    · simp only [NNReal.coe_mul, NNReal.coe_ofNat, hδ]; linarith
    · simpa using hc
  · have hsep := isSeparated_maximalSeparatedSet (ε := 2 * δ) (A := A)
    have hdisj : (↑hSfin.toFinset : Set (Fin n → ℂ)).PairwiseDisjoint (fun c => ball c (r / 4)) := by
      intro x hx y hy hxy
      apply ball_disjoint_ball
      have h1 : ((2 * δ : NNReal) : ENNReal) < edist x y := hsep (by simpa using hx) (by simpa using hy) hxy
      rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)] at h1
      simp only [NNReal.coe_mul, NNReal.coe_ofNat, hδ] at h1
      linarith
    have hsub : (⋃ c ∈ hSfin.toFinset, ball c (r / 4)) ⊆ thickening r A := by
      refine Set.iUnion₂_subset fun c hc => ?_
      exact (ball_subset_thickening (maximalSeparatedSet_subset (by simpa using hc)) _).trans
        (thickening_mono (by linarith) A)
    have hvol := measure_mono (μ := volume) hsub
    rw [measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)] at hvol
    simp only [volume_ball_pi_complex _ (by positivity : (0 : ℝ) < r / 4), Finset.sum_const,
      nsmul_eq_mul] at hvol
    have hfin : volume (thickening r A) ≠ ⊤ := (hA.isBounded.thickening).measure_lt_top.ne
    have := ENNReal.toReal_mono hfin hvol
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity)] at this

theorem SmallSetBallCover.proof (h : SmallSetTubeVolume.Statement) : SmallSetBallCover.Statement := by
  intro n d I K hdim hK
  obtain ⟨C, hC0, hC⟩ := h n d I K hdim hK
  refine ⟨C * (16 / Real.pi) ^ n, by positivity, fun r hr => ?_⟩
  have hr0 := hr.1
  have hZ : IsClosed (zeroSet I) := by
    have : zeroSet I = ⋂ q ∈ I, {x : Fin n → ℂ | eval x q = 0} := by ext x; simp [zeroSet]
    rw [this]
    exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const
  have hA : IsCompact (zeroSet I ∩ K) := hK.inter_left hZ
  obtain ⟨T, hTA, hcov, hcount⟩ := exists_cover_le_volume_thickening hA hr0
  refine ⟨T, hTA, hcov, ?_⟩
  have hV := ENNReal.toReal_le_of_le_ofReal (by positivity) (hC r hr)
  have hz : r ^ ((2 * n + 2 : ℤ) - 2 * d) * r ^ (2 * d) = r ^ (2 * n) * r ^ 2 := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hr0.ne', ← zpow_add₀ hr0.ne']
    congr 1; push_cast; ring
  have hP : 0 < (Real.pi / 16) ^ n * r ^ (2 * n) := by positivity
  have he : (16 / Real.pi) ^ n * (Real.pi / 16) ^ n = 1 := by
    rw [← mul_pow, div_mul_div_comm, mul_comm 16, div_self (by positivity), one_pow]
  have hball : (Real.pi * (r / 4) ^ 2) ^ n = (Real.pi / 16) ^ n * r ^ (2 * n) := by
    rw [pow_mul, ← mul_pow]; ring_nf
  refine le_of_mul_le_mul_right ?_ hP
  calc (T.card : ℝ) * r ^ (2 * d) * ((Real.pi / 16) ^ n * r ^ (2 * n))
      = ((T.card : ℝ) * (Real.pi * (r / 4) ^ 2) ^ n) * r ^ (2 * d) := by rw [hball]; ring
    _ ≤ (C * r ^ ((2 * n + 2 : ℤ) - 2 * d)) * r ^ (2 * d) := mul_le_mul_of_nonneg_right (hcount.trans hV) (by positivity)
    _ = C * (16 / Real.pi) ^ n * r ^ 2 * ((Real.pi / 16) ^ n * r ^ (2 * n)) := by
      rw [mul_assoc, hz]
      linear_combination (-(C * r ^ (2 * n) * r ^ 2)) * he

end

end GroundTheory.Heights₂.Heights
