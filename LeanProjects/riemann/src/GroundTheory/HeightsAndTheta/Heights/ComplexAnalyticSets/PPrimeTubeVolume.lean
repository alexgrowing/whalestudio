import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeTubeVolume
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarietyMassLower
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSmallSetBallCover
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets Metric

noncomputable section

theorem primeTube_isClosed_zeroSet {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroSet J) := by
  have : zeroSet J = ⋂ q ∈ J, {x : Fin n → ℂ | eval x q = 0} := by ext x; simp [zeroSet]
  rw [this]
  exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const

theorem primeTube_isClosed_zeroSetEuc {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) :
    IsClosed (zeroSetEuc J) := by
  have : zeroSetEuc J = ⋂ q ∈ J, {z : EuclideanSpace ℂ (Fin n) | eval (fun i => z i) q = 0} := by
    ext z; simp [zeroSetEuc]
  rw [this]
  exact isClosed_biInter fun q _ =>
    isClosed_eq ((MvPolynomial.continuous_eval q).comp (PiLp.continuous_ofLp 2 _)) continuous_const

theorem primeTube_exists_dim {n k : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : J.IsPrime)
    (hk : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (k : ℕ)) :
    ∃ d : ℕ, d ≤ k ∧ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d : ℕ) := by
  have hnn : 0 ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) := ringKrullDim_nonneg_of_nontrivial
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = x at hnn hk ⊢
  induction x using WithBot.recBotCoe with
  | bot => simp at hnn
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      rw [← WithBot.coe_natCast] at hk
      exact absurd (WithBot.coe_le_coe.1 hk) (by simp)
    | coe m => exact ⟨m, by exact_mod_cast hk, by norm_cast⟩

theorem primeTube_exact (hL : VarietyMassLower.Statement) (hM : MassFinite.Statement) {n d : ℕ}
    {J : Ideal (MvPolynomial (Fin n) ℂ)} {K : Set (Fin n → ℂ)} (hJ : J.IsPrime)
    (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d : ℕ)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Ioc (0 : ℝ) 1,
      volume (thickening r (zeroSet J ∩ K)) ≤ ENNReal.ofReal (C * r ^ ((2 * n : ℤ) - 2 * d)) := by
  set e : (Fin n → ℂ) → EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 with he_def
  have hdist : ∀ x y : Fin n → ℂ, dist x y ≤ dist (e x) (e y) := fun x y =>
    by simpa [he_def] using (PiLp.lipschitzWith_ofLp 2 (fun _ : Fin n => ℂ)).dist_le_mul (e x) (e y)
  obtain ⟨R, hR⟩ := ((hK.image (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ))).isBounded).exists_norm_le
  have hRK : ∀ x ∈ K, ‖e x‖ ≤ R := fun x hx => hR _ ⟨x, hx, rfl⟩
  obtain ⟨c, hc0, hc⟩ := hL n d J hJ hd R
  set M : ENNReal := μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ ball (0 : EuclideanSpace ℂ (Fin n)) (R + 1))
  have hMfin : M ≠ ⊤ := (hM n d J hJ hd (R + 1)).ne
  refine ⟨M.toReal * 4 ^ d * (4 * Real.pi) ^ n / c, by positivity, fun r hr => ?_⟩
  obtain ⟨hr0, hr1⟩ := hr
  set S := zeroSet J ∩ K
  have hS : IsCompact S := hK.inter_left (primeTube_isClosed_zeroSet J)

  set δ : NNReal := (r / 2).toNNReal
  have hδ : ((2 * δ : NNReal) : ℝ) = r := by
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity)]; push_cast; ring
  have hpack : packingNumber (2 * δ) S ≠ ⊤ := by
    obtain ⟨N, -, hNfin, hN⟩ := exists_finite_isCover_of_isCompact (ε := δ)
      (by rw [ne_eq, ← NNReal.coe_eq_zero, Real.coe_toNNReal _ (by positivity)]; exact (by positivity : r / 2 ≠ 0)) hS
    exact ne_top_of_le_ne_top (Set.encard_ne_top_iff.2 hNfin)
      ((packingNumber_two_mul_le_externalCoveringNumber δ S).trans hN.externalCoveringNumber_le_encard)
  set T0 := maximalSeparatedSet (2 * δ) S
  have hTfin : T0.Finite :=
    Set.encard_ne_top_iff.1 (by rw [encard_maximalSeparatedSet hpack]; exact hpack)
  set T := hTfin.toFinset
  have hTS : ∀ t ∈ T, t ∈ S := fun t ht => maximalSeparatedSet_subset (by simpa [T] using ht)

  have hcov : thickening r S ⊆ ⋃ t ∈ T, ball t (2 * r) := by
    intro p hp
    obtain ⟨s, hs, hps⟩ := mem_thickening_iff.1 hp
    have hs' := (isCover_maximalSeparatedSet hpack).subset_iUnion_closedBall hs
    obtain ⟨t, ht, hst⟩ := Set.mem_iUnion₂.1 hs'
    rw [mem_closedBall, hδ] at hst
    refine Set.mem_iUnion₂.2 ⟨t, by simpa [T] using ht, ?_⟩
    rw [mem_ball]
    linarith [dist_triangle p s t]
  have hvol : volume (thickening r S) ≤ ENNReal.ofReal ((T.card : ℝ) * (Real.pi * (2 * r) ^ 2) ^ n) := by
    refine (measure_mono hcov).trans ((measure_biUnion_finset_le T _).trans (le_of_eq ?_))
    simp only [volume_ball_pi_complex _ (by positivity : (0 : ℝ) < 2 * r), Finset.sum_const, nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]

  have hsep := isSeparated_maximalSeparatedSet (ε := 2 * δ) (A := S)
  have hdisj : (↑T : Set (Fin n → ℂ)).PairwiseDisjoint (fun t => zeroSetEuc J ∩ ball (e t) (r / 2)) := by
    intro x hx y hy hxy
    refine Set.disjoint_left.2 fun z hzx hzy => ?_
    have h1 : ((2 * δ : NNReal) : ENNReal) < edist x y := hsep (by simpa [T] using hx) (by simpa [T] using hy) hxy
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity), hδ] at h1
    have h2 := dist_triangle_left (e x) (e y) z
    simp only [Set.mem_inter_iff, mem_ball] at hzx hzy
    linarith [hdist x y, hzx.2, hzy.2]
  have hsub : (⋃ t ∈ T, zeroSetEuc J ∩ ball (e t) (r / 2)) ⊆
      zeroSetEuc J ∩ ball (0 : EuclideanSpace ℂ (Fin n)) (R + 1) := by
    refine Set.iUnion₂_subset fun t ht => fun z ⟨hz, hzt⟩ => ⟨hz, ?_⟩
    rw [mem_ball_zero_iff]
    rw [mem_ball, dist_eq_norm] at hzt
    have := hRK t (hTS t ht).2
    have := norm_le_norm_add_norm_sub' z (e t)
    linarith
  have hmass : (T.card : ENNReal) * ENNReal.ofReal (c * (r / 2) ^ (2 * d)) ≤ M := by
    refine le_trans ?_ (measure_mono hsub)
    rw [measure_biUnion_finset hdisj fun t _ =>
      (primeTube_isClosed_zeroSetEuc J).measurableSet.inter measurableSet_ball]
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun t ht => hc (e t) ?_ (hRK t (hTS t ht).2) (r / 2) ⟨by positivity, by linarith⟩
    have htZ := (hTS t ht).1
    intro q hq
    simpa [he_def] using htZ q hq
  have hcount : (T.card : ℝ) * (c * (r / 2) ^ (2 * d)) ≤ M.toReal := by
    have := ENNReal.toReal_mono hMfin hmass
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity)] at this

  refine hvol.trans (ENNReal.ofReal_le_ofReal ?_)
  set Y : ℝ := r ^ ((2 * n : ℤ) - 2 * d)
  have hY : Y * r ^ (2 * d) = r ^ (2 * n) := by
    simp only [Y]
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hr0.ne']
    congr 1; push_cast; ring
  have h4 : (r / 2) ^ (2 * d) * 4 ^ d = r ^ (2 * d) := by
    rw [div_pow, pow_mul, pow_mul]; field_simp; norm_num
  have hX : (T.card : ℝ) * (Real.pi * (2 * r) ^ 2) ^ n =
      (T.card : ℝ) * (c * (r / 2) ^ (2 * d)) * ((4 : ℝ) ^ d * (4 * Real.pi) ^ n * Y / c) := by
    rw [← h4] at hY
    have hX' : (Real.pi * (2 * r) ^ 2) ^ n = (4 * Real.pi) ^ n * r ^ (2 * n) := by
      rw [pow_mul, ← mul_pow]; ring
    rw [hX', ← hY]
    field_simp
  rw [hX]
  calc (T.card : ℝ) * (c * (r / 2) ^ (2 * d)) * ((4 : ℝ) ^ d * (4 * Real.pi) ^ n * Y / c)
      ≤ M.toReal * ((4 : ℝ) ^ d * (4 * Real.pi) ^ n * Y / c) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = M.toReal * 4 ^ d * (4 * Real.pi) ^ n / c * Y := by ring

theorem PrimeTubeVolume.proof (hL : VarietyMassLower.Statement) (hM : MassFinite.Statement) :
    PrimeTubeVolume.Statement := by
  intro n k J K hJ hk hK
  obtain ⟨d, hdk, hd⟩ := primeTube_exists_dim hJ hk
  obtain ⟨C, hC, hCr⟩ := primeTube_exact hL hM hJ hd hK
  refine ⟨C, hC, fun r hr => (hCr r hr).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hC))⟩
  exact zpow_le_zpow_right_of_le_one₀ hr.1 hr.2 (by omega)

end

end GroundTheory.Heights₂.Heights
