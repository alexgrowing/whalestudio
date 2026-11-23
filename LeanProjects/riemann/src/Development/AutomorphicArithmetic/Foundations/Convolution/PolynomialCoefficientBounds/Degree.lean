import Mathlib

open MvPolynomial Filter Topology

private theorem UpperTheory.ConvolutionTheory.FX.exp_le_factorial_eventually (k : ℕ) (hk : k ≠ 0) :
    ∀ᶠ j : ℕ in atTop, Real.exp ((k : ℝ) * j) ≤ ((j / k).factorial : ℝ) := by
  set C : ℝ := Real.exp ((k : ℝ) * k) with hC
  have hCpos : 0 < C := Real.exp_pos _
  have h1 : ∀ᶠ n : ℕ in atTop, C ^ n / (n.factorial : ℝ) ≤ 1 / C :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop C).eventually
      (ge_mem_nhds (by positivity))
  have h2 : ∀ᶠ n : ℕ in atTop, C ^ (n + 1) ≤ (n.factorial : ℝ) := by
    filter_upwards [h1] with n hn
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    rw [div_le_div_iff₀ hf hCpos] at hn
    rw [pow_succ]
    linarith
  filter_upwards [(Nat.tendsto_div_const_atTop hk).eventually h2] with j hj
  refine le_trans ?_ hj
  rw [hC, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have h3 : j ≤ k * (j / k + 1) := (Nat.lt_mul_div_succ j (Nat.pos_of_ne_zero hk)).le
  have h4 : (j : ℝ) ≤ k * ((j / k + 1 : ℕ) : ℝ) := by exact_mod_cast h3
  have h5 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc (k : ℝ) * j ≤ k * (k * ((j / k + 1 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left h4 h5
    _ = _ := by ring

theorem UpperTheory.ConvolutionTheory.FX.degree :
    ∃ d : ℕ → ℕ, Tendsto (fun j : ℕ => (d j : ℝ) / j) atTop (𝓝 0) ∧ ∀ B : ℝ, ∀ᶠ j : ℕ in atTop, Real.exp (B * j) ≤ (d j).factorial := by
  classical
  let P : ℕ → ℕ → Prop := fun j k => Real.exp ((k : ℝ) * j) ≤ ((j / k).factorial : ℝ)
  let κ : ℕ → ℕ := fun j => Nat.findGreatest (P j) j
  have hκ : ∀ K : ℕ, K ≠ 0 → ∀ᶠ j : ℕ in atTop, K ≤ κ j ∧ P j (κ j) := by
    intro K hK
    filter_upwards [UpperTheory.ConvolutionTheory.FX.exp_le_factorial_eventually K hK, eventually_ge_atTop K] with j h1 h2
    exact ⟨Nat.le_findGreatest h2 h1, Nat.findGreatest_spec (P := P j) h2 h1⟩
  have hlim : Tendsto κ atTop atTop := by
    refine tendsto_atTop.mpr fun K => ?_
    filter_upwards [hκ (K + 1) (Nat.succ_ne_zero K)] with j hj
    exact le_trans (Nat.le_succ K) hj.1
  refine ⟨fun j => j / κ j, ?_, fun B => ?_⟩
  · have h0 : Tendsto (fun j : ℕ => ((κ j : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hlim)
    refine squeeze_zero' (Eventually.of_forall fun j => by positivity) ?_ h0
    filter_upwards [eventually_gt_atTop 0] with j hj
    have hj' : (0 : ℝ) < j := by exact_mod_cast hj
    rw [div_le_iff₀ hj', inv_mul_eq_div]
    exact Nat.cast_div_le
  · filter_upwards [hκ (⌈B⌉₊ + 1) (Nat.succ_ne_zero _)] with j hj
    refine le_trans (Real.exp_le_exp.mpr ?_) hj.2
    have h1 : ((⌈B⌉₊ + 1 : ℕ) : ℝ) ≤ κ j := by exact_mod_cast hj.1
    have h2 : B ≤ ⌈B⌉₊ := Nat.le_ceil B
    push_cast at h1
    exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg j)
