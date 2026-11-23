import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IntegralTraceNormBounds

namespace ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation

open NumberField InfinitePlace Module MeasureTheory Metric TraceIntegralBasis IntegralTraceNormBounds
open scoped Classical

theorem pack {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W]
    [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W] (μ : Measure W) [μ.IsAddHaarMeasure]
    (S : Finset W) (R : ℝ) (hR : 0 ≤ R) (hS : ∀ p ∈ S, ‖p‖ ≤ R)
    (hsep : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → 1 ≤ ‖p - q‖) :
    (S.card : ℝ) ≤ (1 + 2 * R) ^ finrank ℝ W := by
  set d := finrank ℝ W
  have hdisj : (S : Set W).PairwiseDisjoint fun p => ball p (1 / 2) := by
    intro p hp q hq hpq
    rw [Function.onFun, Set.disjoint_left]
    intro z hzp hzq
    rw [mem_ball, dist_eq_norm] at hzp hzq
    have h1 := hsep p hp q hq hpq
    have h2 : ‖p - q‖ ≤ ‖z - p‖ + ‖z - q‖ := by
      calc ‖p - q‖ = ‖(z - q) - (z - p)‖ := by congr 1; abel
        _ ≤ ‖z - q‖ + ‖z - p‖ := norm_sub_le _ _
        _ = ‖z - p‖ + ‖z - q‖ := add_comm _ _
    linarith
  have hsub : (⋃ p ∈ S, ball p (1 / 2)) ⊆ ball (0 : W) (R + 1 / 2) := by
    intro z hz
    simp only [Set.mem_iUnion, mem_ball, dist_eq_norm] at hz
    obtain ⟨p, hp, hzp⟩ := hz
    rw [mem_ball, dist_eq_norm, sub_zero]
    calc ‖z‖ = ‖(z - p) + p‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - p‖ + ‖p‖ := norm_add_le _ _
      _ < 1 / 2 + R := by linarith [hS p hp]
      _ = R + 1 / 2 := add_comm _ _
  have h := measure_mono (μ := μ) hsub
  rw [measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)] at h
  simp only [Measure.addHaar_ball μ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    Measure.addHaar_ball μ _ (by positivity : (0 : ℝ) ≤ R + 1 / 2), Finset.sum_const,
    nsmul_eq_mul] at h
  rw [← mul_assoc] at h
  have hc0 : μ (ball 0 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hctop : μ (ball 0 1) ≠ ⊤ := measure_ball_lt_top.ne
  have h2 := (ENNReal.mul_le_mul_iff_left hc0 hctop).mp h
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
  have h3 : (S.card : ℝ) = (S.card : ℝ) * (1 / 2) ^ d * 2 ^ d := by
    rw [mul_assoc, ← mul_pow]
    norm_num
  rw [h3]
  calc (S.card : ℝ) * (1 / 2) ^ d * 2 ^ d ≤ (R + 1 / 2) ^ d * 2 ^ d :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = (1 + 2 * R) ^ d := by
        rw [← mul_pow]
        congr 1
        ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma one_le_abs_norm (γ : 𝓞 E) (hγ : γ ≠ 0) : 1 ≤ |(Algebra.norm ℚ (γ : E) : ℝ)| := by
  have h := Algebra.coe_norm_int γ
  have hne : Algebra.norm ℤ γ ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero] at h
    exact (Algebra.norm_ne_zero_iff.mpr (by exact_mod_cast hγ : (γ : E) ≠ 0)) h.symm
  rw [← h]
  have := Int.one_le_abs hne
  push_cast
  exact_mod_cast this

lemma sep (γ : 𝓞 E) (hγ : γ ≠ 0) : ∃ w : CP E, 1 ≤ ‖w.1.embedding (γ : E)‖ := by
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace E))
  set w1 : CP E := ⟨w0, IsTotallyComplex.isComplex w0⟩
  have h := prod_norm (E := E) (γ : E)
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w1)] at h
  have hle : ∏ w ∈ Finset.univ.erase w1, ‖w.1.embedding (γ : E)‖ ^ 2 ≤ 1 :=
    Finset.prod_le_one (fun _ _ => by positivity)
      (fun w _ => pow_le_one₀ (norm_nonneg _) (hcon w).le)
  have hlt : ‖w1.1.embedding (γ : E)‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg _) (hcon w1) two_ne_zero
  have := one_le_abs_norm γ hγ
  rw [← h] at this
  nlinarith [mul_le_of_le_one_right (sq_nonneg ‖w1.1.embedding (γ : E)‖) hle]

theorem count (R : ℝ) (hR : 0 ≤ R) :
    {α : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (α : E)‖ ≤ R}.Finite ∧
      ({α : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (α : E)‖ ≤ R}.ncard : ℝ) ≤ (1 + 2 * R) ^ (2 * fdeg E) := by
  set T := {α : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (α : E)‖ ≤ R}
  have hT : T.Finite := by
    have h := Embeddings.finite_of_norm_le E ℂ R
    refine (h.preimage (Set.injOn_of_injective RingOfIntegers.coe_injective)).subset ?_
    intro α hα
    exact ⟨α.isIntegral_coe, hα⟩
  refine ⟨hT, ?_⟩
  let p : 𝓞 E → (CP E → ℂ) := fun α w => w.1.embedding (α : E)
  have hpinj : Function.Injective p := by
    intro α β h
    obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace E))
    have := congrFun h ⟨w0, IsTotallyComplex.isComplex w0⟩
    exact RingOfIntegers.coe_injective (w0.embedding.injective this)
  have hd : finrank ℝ (CP E → ℂ) = 2 * fdeg E := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, (card_CP (E := E)).1, mul_comm]
  have hcard : T.ncard = (hT.toFinset.image p).card := by
    rw [Finset.card_image_of_injective _ hpinj, Set.ncard_eq_toFinset_card _ hT]
  obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace E))
  have : Nonempty (CP E) := ⟨⟨w0, IsTotallyComplex.isComplex w0⟩⟩
  rw [hcard, ← hd]
  refine pack volume _ R hR ?_ ?_
  · intro q hq
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hq
    rw [Set.Finite.mem_toFinset] at hα
    exact (pi_norm_le_iff_of_nonneg hR).mpr fun w => hα _
  · intro q hq q' hq' hne
    obtain ⟨α, -, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨β, -, rfl⟩ := Finset.mem_image.mp hq'
    have hαβ : α - β ≠ 0 := sub_ne_zero.mpr fun h => hne (by rw [h])
    obtain ⟨w, hw⟩ := sep (α - β) hαβ
    calc (1 : ℝ) ≤ ‖w.1.embedding ((α - β : 𝓞 E) : E)‖ := hw
      _ = ‖(p α - p β) w‖ := by simp [p]
      _ ≤ ‖p α - p β‖ := norm_le_pi_norm _ w

end ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation
