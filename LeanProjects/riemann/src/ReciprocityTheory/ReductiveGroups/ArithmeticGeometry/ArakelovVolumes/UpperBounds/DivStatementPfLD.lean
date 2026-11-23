import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivStatementPfLB

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Asymptotics

noncomputable section

variable {n : ℕ}

theorem comp_O (L : V n ≃L[ℂ] V n) (k : Fin n) :
    (fun z : V n => (L z) k) =O[𝓝 0] fun z => ‖z‖ := by
  have h1 : (fun z : V n => L z) =O[𝓝 0] fun z => z := (L : V n →L[ℂ] V n).isBigO_id _
  have h2 : (fun z : V n => (L z) k) =O[𝓝 0] fun z => L z := by
    refine IsBigO.of_bound 1 (Filter.Eventually.of_forall fun z => ?_)
    rw [one_mul]
    first
      | exact norm_le_pi_norm (L z) k
      | exact PiLp.norm_apply_le (L z) k
      | simpa using norm_le_pi_norm (L z) k
  exact (h2.trans h1).trans (isBigO_norm_right.mpr (isBigO_refl _ _))

theorem sub_val_O {g : V n → ℂ} (hg : AnalyticAt ℂ g 0) :
    (fun z => g 0 - g z) =O[𝓝 0] fun z => ‖z‖ ^ 1 := by
  have h := hg.differentiableAt.hasFDerivAt.isBigO_sub
  simp only [sub_zero] at h
  have h2 := h.neg_left
  simp only [neg_sub] at h2
  simp only [pow_one]
  exact h2.trans (isBigO_norm_right.mpr (isBigO_refl _ _))

theorem local_step {δ T d : ℕ} (hd : d ≤ T) (W : V n → ℂ) (S : Fin n → V n → ℂ)
    (Tt : Fin δ → V n → ℂ) (L : V n ≃L[ℂ] V n)
    (hW : AnalyticAt ℂ W 0) (hW0 : W 0 ≠ 0) (hS : ∀ k, AnalyticAt ℂ (S k) 0) (hS0 : ∀ k, S k 0 = 0)
    (hT : ∀ k, AnalyticAt ℂ (Tt k) 0)
    (hL : ∀ k z, (L z) k = fderiv ℂ (fun y => S k y / W y) 0 z)
    (G : V n → ℂ) (hG : AnalyticAt ℂ G 0) (hGO : G =O[𝓝 0] fun z => ‖z‖ ^ d) :
    ∃ a : (Fin n → ℕ) → ℂ, ∀ c : (Fin n → ℕ) → Fin δ → ℂ,
      (∀ α ∈ Finset.Nat.antidiagonalTuple n d, ∑ k, c α k * Tt k 0 * W 0 ^ T = a α) →
      (fun z => G z - ∑ α ∈ Finset.Nat.antidiagonalTuple n d,
        ∑ k, c α k * (∏ i, S i z ^ α i) * W z ^ (T - d) * Tt k z) =O[𝓝 0]
        fun z => ‖z‖ ^ (d + 1) := by
  obtain ⟨q, hq⟩ := taylor_step hG hGO
  obtain ⟨a, ha⟩ := multilinear_expand q L
  refine ⟨a, fun c hc => ?_⟩
  have hWev : ∀ᶠ z in 𝓝 (0 : V n), W z ≠ 0 := hW.continuousAt.eventually_ne hW0
  have hφan : ∀ i, AnalyticAt ℂ (fun y => S i y / W y) 0 := fun i => (hS i).div hW hW0
  have hφℓ : ∀ i, (fun z => S i z / W z - (L z) i) =O[𝓝 0] fun z => ‖z‖ ^ 2 := by
    intro i
    exact (taylor2 (hφan i)).congr' (Filter.Eventually.of_forall fun z => by
      simp only [hS0 i, zero_div, sub_zero, ← hL i z]) Filter.EventuallyEq.rfl
  have hℓO : ∀ i, (fun z => (L z) i) =O[𝓝 0] fun z => ‖z‖ := fun i => comp_O L i
  have hφO : ∀ i, (fun z => S i z / W z) =O[𝓝 0] fun z => ‖z‖ := by
    intro i
    have h2 : (fun z => S i z / W z - (L z) i) =O[𝓝 0] fun z => ‖z‖ :=
      ((hφℓ i).trans (isBigO_norm_pow_of_le (F := V n) (by norm_num : 1 ≤ 2))).congr'
        Filter.EventuallyEq.rfl (Filter.Eventually.of_forall fun z => pow_one _)
    exact (h2.add (hℓO i)).congr' (Filter.Eventually.of_forall fun z => sub_add_cancel _ _)
      Filter.EventuallyEq.rfl
  have hprodO : ∀ u : Fin n → V n → ℂ, (∀ i, u i =O[𝓝 0] fun z => ‖z‖) →
      ∀ (e : Fin n → ℕ) (s : Finset (Fin n)),
        (fun z => ∏ i ∈ s, u i z ^ e i) =O[𝓝 0] fun z => ‖z‖ ^ (∑ i ∈ s, e i) := by
    intro u hu e s
    induction s using Finset.induction_on with
    | empty =>
      exact (isBigO_const_const (1 : ℂ) (one_ne_zero : (1 : ℝ) ≠ 0) (𝓝 (0 : V n))).congr'
        (Filter.Eventually.of_forall fun z => by simp) (Filter.Eventually.of_forall fun z => by simp)
    | insert a s ha ih =>
      refine (((hu a).pow (e a)).mul ih).congr' (Filter.Eventually.of_forall fun z => ?_)
        (Filter.Eventually.of_forall fun z => ?_)
      · simp only [Finset.prod_insert ha]
      · simp only [Finset.sum_insert ha, pow_add]
  have hsplit : (fun z => G z - ∑ α ∈ Finset.Nat.antidiagonalTuple n d,
        ∑ k, c α k * (∏ i, S i z ^ α i) * W z ^ (T - d) * Tt k z) =
      fun z => (G z - q (fun _ => z)) + ∑ α ∈ Finset.Nat.antidiagonalTuple n d,
        (a α * ∏ k, (L z) k ^ α k - ∑ k, c α k * (∏ i, S i z ^ α i) * W z ^ (T - d) * Tt k z) := by
    funext z
    rw [Finset.sum_sub_distrib, ← ha z]
    ring
  have hsum : ∀ α ∈ Finset.Nat.antidiagonalTuple n d,
      (fun z => a α * ∏ k, (L z) k ^ α k -
        ∑ k, c α k * (∏ i, S i z ^ α i) * W z ^ (T - d) * Tt k z) =O[𝓝 0]
        fun z => ‖z‖ ^ (d + 1) := by
    intro α hα
    have hsumα : ∑ i, α i = d := Finset.Nat.mem_antidiagonalTuple.mp hα
    have hsumAn : AnalyticAt ℂ (fun z => ∑ k, c α k * Tt k z) 0 := by
      have hfun : (fun z => ∑ k, c α k * Tt k z) = ∑ k, fun z => c α k * Tt k z := by
        funext z
        simp [Finset.sum_apply]
      rw [hfun]
      exact Finset.analyticAt_sum Finset.univ fun k _ => analyticAt_const.mul (hT k)
    have hH : AnalyticAt ℂ (fun z => W z ^ T * ∑ k, c α k * Tt k z) 0 := by
      exact (hW.pow T).mul hsumAn
    have hH0 : W 0 ^ T * ∑ k, c α k * Tt k 0 = a α := by
      rw [← hc α hα, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hdiffH := sub_val_O hH
    have hP := prod_pow_sub Finset.univ (fun i z => (L z) i) (fun i z => S i z / W z) α hℓO hφO
      (fun i => (hφℓ i).neg_left.congr' (Filter.Eventually.of_forall fun z => by
        first
        | ring
        | (simp only []; ring)) Filter.EventuallyEq.rfl)
    have hφα := hprodO (fun i z => S i z / W z) hφO α Finset.univ
    have hmain : (fun z => a α * (∏ i, (L z) i ^ α i - ∏ i, (S i z / W z) ^ α i) +
        (∏ i, (S i z / W z) ^ α i) *
          (W 0 ^ T * ∑ k, c α k * Tt k 0 - W z ^ T * ∑ k, c α k * Tt k z)) =O[𝓝 0]
        fun z => ‖z‖ ^ (d + 1) := by
      refine IsBigO.add ?_ ?_
      · exact (hP.const_mul_left (a α)).congr' (Filter.Eventually.of_forall fun z => rfl)
          (Filter.Eventually.of_forall fun z => by simp only [hsumα])
      · exact (hφα.mul hdiffH).congr' (Filter.Eventually.of_forall fun z => rfl)
          (Filter.Eventually.of_forall fun z => by
            simp only [pow_one]
            rw [← pow_succ, hsumα])
    refine hmain.congr' (hWev.mono fun z hz => ?_) Filter.EventuallyEq.rfl
    have hSz : ∏ i, S i z ^ α i = (∏ i, (S i z / W z) ^ α i) * W z ^ d := by
      rw [← hsumα, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← mul_pow, div_mul_cancel₀ _ hz]
    have hWT : W z ^ T = W z ^ d * W z ^ (T - d) := by
      rw [← pow_add, Nat.add_sub_cancel' hd]
    have hsumk : ∑ k, c α k * ((∏ i, (S i z / W z) ^ α i) * W z ^ d) * W z ^ (T - d) * Tt k z =
        (∏ i, (S i z / W z) ^ α i) * (W z ^ T * ∑ k, c α k * Tt k z) := by
      rw [hWT, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    beta_reduce
    rw [hH0, hSz, hsumk]
    ring
  rw [hsplit]
  exact hq.add ((IsBigO.sum hsum).congr'
    (Filter.Eventually.of_forall fun z => by simp only [Finset.sum_apply]) Filter.EventuallyEq.rfl)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
