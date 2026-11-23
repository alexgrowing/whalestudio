import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
open Filter Topology GlobalTheory.VolBr

namespace GlobalTheory

theorem eventually_le_of_poly_asymptotics :
    ∀ (d b : ℕ) (f : ℝ → ℕ → ℝ) (g : ℕ → ℝ) (α β : ℝ), 0 < d → 0 < b →
      (∀ η, 0 ≤ η → Tendsto (fun j : ℕ => f η j / (j : ℝ) ^ d) atTop (𝓝 (α + β * η))) →
      (∀ η, 0 < η → ∀ᶠ j : ℕ in atTop, g j ≤ f η j) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
        g ((b * n + 1) * m) ≤ f 0 (b * n * m) + ε * ((n : ℝ) * m) ^ d := by
  intro d b f g α β _hd hb hf hg ε hε
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hc : (0 : ℝ) < (b : ℝ) ^ d := pow_pos hbR d
  obtain ⟨η, θ, hη, hθ, key⟩ : ∃ η θ : ℝ, 0 < η ∧ 0 < θ ∧ (β * η + 2 * θ) * (b : ℝ) ^ d < ε := by
    generalize (b : ℝ) ^ d = c at hc ⊢
    have hβ1 : (0 : ℝ) < |β| + 1 := by positivity
    refine ⟨ε / (4 * c * (|β| + 1)), ε / (8 * c), div_pos hε (by positivity),
      div_pos hε (by positivity), ?_⟩
    have e1 : (|β| + 1) * (ε / (4 * c * (|β| + 1))) * c = ε / 4 := by
      field_simp
    have e2 : ε / (8 * c) * c = ε / 8 := by
      field_simp
    have h1 : β * (ε / (4 * c * (|β| + 1))) * c ≤ |β| * (ε / (4 * c * (|β| + 1))) * c :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self β)
        (div_pos hε (by positivity)).le) hc.le
    have h2 : 0 < ε / (4 * c * (|β| + 1)) * c := mul_pos (div_pos hε (by positivity)) hc
    nlinarith
  set A : ℝ := α + β * η + θ with hAdef
  set B : ℝ := α - θ with hBdef
  have hlim : Tendsto (fun n : ℕ => A * ((b : ℝ) + 1 / (n : ℝ)) ^ d) atTop (𝓝 (A * (b : ℝ) ^ d)) := by
    have := ((tendsto_one_div_atTop_nhds_zero_nat.const_add (b : ℝ)).pow d).const_mul A
    simpa using this
  have hn : ∀ᶠ n : ℕ in atTop, A * ((b : ℝ) + 1 / (n : ℝ)) ^ d < B * (b : ℝ) ^ d + ε :=
    (tendsto_order.1 hlim).2 _ (by rw [hAdef, hBdef]; nlinarith)
  have hAe : ∀ᶠ j : ℕ in atTop, f η j / (j : ℝ) ^ d < A :=
    (tendsto_order.1 (hf η hη.le)).2 A (by rw [hAdef]; linarith)
  have hBe : ∀ᶠ j : ℕ in atTop, B < f 0 j / (j : ℝ) ^ d :=
    (tendsto_order.1 (hf 0 le_rfl)).1 B (by rw [hBdef, mul_zero, add_zero]; linarith)
  filter_upwards [hn, eventually_ge_atTop 1] with n hn hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hk : Tendsto (fun m : ℕ => (b * n + 1) * m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m (Nat.succ_pos _)) tendsto_id
  have hk' : Tendsto (fun m : ℕ => b * n * m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m (Nat.mul_pos hb hn1)) tendsto_id
  filter_upwards [hk.eventually (hAe.and (hg η hη)), hk'.eventually hBe, eventually_gt_atTop 0]
    with m ⟨hA1, hG1⟩ hB1 hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hj : (((b * n + 1) * m : ℕ) : ℝ) = ((b : ℝ) + 1 / (n : ℝ)) * ((n : ℝ) * m) := by
    push_cast
    rw [show ((b : ℝ) + 1 / (n : ℝ)) * ((n : ℝ) * (m : ℝ))
        = (b : ℝ) * n * m + ((n : ℝ)⁻¹ * (n : ℝ)) * m by ring, inv_mul_cancel₀ hnR.ne']
    ring
  have hj' : ((b * n * m : ℕ) : ℝ) = (b : ℝ) * ((n : ℝ) * m) := by push_cast; ring
  have hjpos : (0 : ℝ) < (((b * n + 1) * m : ℕ) : ℝ) := by
    rw [hj]; positivity
  have hj'pos : (0 : ℝ) < ((b * n * m : ℕ) : ℝ) := by
    rw [hj']; positivity
  have hnm : (0 : ℝ) < ((n : ℝ) * m) ^ d := pow_pos (mul_pos hnR hmR) d
  have hA2 := (div_lt_iff₀ (pow_pos hjpos d)).1 hA1
  have hB2 := (lt_div_iff₀ (pow_pos hj'pos d)).1 hB1
  calc g ((b * n + 1) * m) ≤ f η ((b * n + 1) * m) := hG1
    _ ≤ A * ((((b * n + 1) * m : ℕ) : ℝ)) ^ d := hA2.le
    _ = (A * ((b : ℝ) + 1 / (n : ℝ)) ^ d) * ((n : ℝ) * m) ^ d := by rw [hj, mul_pow]; ring
    _ ≤ (B * (b : ℝ) ^ d + ε) * ((n : ℝ) * m) ^ d := mul_le_mul_of_nonneg_right hn.le hnm.le
    _ = B * (((b * n * m : ℕ) : ℝ)) ^ d + ε * ((n : ℝ) * m) ^ d := by rw [hj', mul_pow]; ring
    _ ≤ f 0 (b * n * m) + ε * ((n : ℝ) * m) ^ d := by linarith

end GlobalTheory
