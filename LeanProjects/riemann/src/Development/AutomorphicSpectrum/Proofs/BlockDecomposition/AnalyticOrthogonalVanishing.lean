import Mathlib

namespace GlobalTheory.CompanionTheory.VectorTaylor

open Filter Topology

theorem factorial_add_le (k n : ℕ) :
    ((k + n).factorial : ℝ) ≤ 2 ^ (k + n) * k.factorial * n.factorial := by
  have h1 : (k + n).factorial = (k + n).choose n * k.factorial * n.factorial :=
    (Nat.add_choose_mul_factorial_mul_factorial k n).symm
  have h2 : (k + n).choose n ≤ 2 ^ (k + n) := Nat.choose_le_two_pow _ _
  have h3 : (k + n).factorial ≤ 2 ^ (k + n) * k.factorial * n.factorial := by
    rw [h1]
    gcongr
  exact_mod_cast h3

private theorem norm_le_pow_succ_div_factorial_of_deriv_bound (g g' : ℝ → ℂ) (a : ℝ) (n : ℕ)
    (hg : ∀ σ, HasDerivAt g (g' σ) σ) (hg0 : g 0 = 0)
    (hb : ∀ σ, 0 ≤ σ → ‖g' σ‖ ≤ a * σ ^ n / n.factorial) (x : ℝ) (hx : 0 ≤ x) :
    ‖g x‖ ≤ a * x ^ (n + 1) / (n + 1).factorial := by
  have hB : ∀ σ, HasDerivAt (fun σ : ℝ => a * σ ^ (n + 1) / (n + 1).factorial)
      (a * σ ^ n / n.factorial) σ := by
    intro σ
    have h := ((hasDerivAt_pow (n + 1) σ).const_mul a).div_const ((n + 1).factorial : ℝ)
    refine h.congr_deriv ?_
    rw [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul]
    have hn : (n.factorial : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := g) (f' := g') (a := 0) (b := x)
    (fun σ _ => (hg σ).continuousAt.continuousWithinAt)
    (fun σ _ => (hg σ).hasDerivWithinAt) (by simp [hg0]) hB
    (fun σ hσ => hb σ hσ.1) ⟨hx, le_rfl⟩

theorem iter_bound (f : ℕ → ℝ → ℂ) (A : ℕ → ℝ)
    (hd : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t)
    (hb : ∀ k t, ‖f k t‖ ≤ A k) (t₀ : ℝ) (h0 : ∀ k, f k t₀ = 0) (n : ℕ) :
    ∀ k s, ‖f k (t₀ + s)‖ ≤ A (k + n) * |s| ^ n / n.factorial := by
  induction n with
  | zero =>
    intro k s
    simpa using hb k (t₀ + s)
  | succ n ih =>
    intro k s
    have hA : A (k + 1 + n) = A (k + (n + 1)) := by congr 1; omega
    rcases le_total 0 s with hs | hs
    · have h := norm_le_pow_succ_div_factorial_of_deriv_bound (fun σ => f k (t₀ + σ)) (fun σ => f (k + 1) (t₀ + σ))
        (A (k + (n + 1))) n (fun σ => (hd k (t₀ + σ)).comp_const_add t₀ σ) (by simpa using h0 k)
        (fun σ hσ => by
          have := ih (k + 1) σ
          rwa [hA, abs_of_nonneg hσ] at this) s hs
      rwa [abs_of_nonneg hs]
    · have h := norm_le_pow_succ_div_factorial_of_deriv_bound (fun σ => f k (t₀ - σ)) (fun σ => -f (k + 1) (t₀ - σ))
        (A (k + (n + 1))) n (fun σ => (hd k (t₀ - σ)).comp_const_sub t₀ σ) (by simpa using h0 k)
        (fun σ hσ => by
          have := ih (k + 1) (-σ)
          rw [hA, abs_neg, abs_of_nonneg hσ, ← sub_eq_add_neg] at this
          rwa [norm_neg]) (-s) (by linarith)
      rw [abs_of_nonpos hs]
      simpa [sub_neg_eq_add] using h

theorem step (f : ℕ → ℝ → ℂ) (B D : ℝ) (hB : 0 ≤ B) (hD : 1 ≤ D)
    (hd : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t)
    (hb : ∀ k t, ‖f k t‖ ≤ B * D ^ k * (k.factorial : ℝ)) (t₀ : ℝ) (h0 : ∀ k, f k t₀ = 0)
    (s : ℝ) (hs : |s| ≤ 1 / (4 * D)) (k : ℕ) : f k (t₀ + s) = 0 := by
  have hD0 : 0 < D := by linarith
  have h2Ds : 2 * D * |s| ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 2 * D)
    calc 2 * D * |s| ≤ 2 * D * (1 / (4 * D)) := h
      _ = 1 / 2 := by field_simp; ring
  have hbound : ∀ n : ℕ, ‖f k (t₀ + s)‖ ≤ B * (2 * D) ^ k * k.factorial * (1 / 2) ^ n := by
    intro n
    have hA := iter_bound f (fun k => B * D ^ k * (k.factorial : ℝ)) hd hb t₀ h0 n k s
    have hfact := factorial_add_le k n
    have hn : (n.factorial : ℝ) ≠ 0 := by positivity
    calc ‖f k (t₀ + s)‖ ≤ B * D ^ (k + n) * ((k + n).factorial : ℝ) * |s| ^ n / n.factorial := hA
      _ ≤ B * D ^ (k + n) * (2 ^ (k + n) * k.factorial * n.factorial) * |s| ^ n / n.factorial := by
          gcongr
      _ = B * (2 * D) ^ k * k.factorial * (2 * D * |s|) ^ n := by
          field_simp
          ring
      _ ≤ B * (2 * D) ^ k * k.factorial * (1 / 2) ^ n := by
          gcongr
  have hlim : Tendsto (fun n : ℕ => B * (2 * D) ^ k * k.factorial * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (B * (2 * D) ^ k * k.factorial)
  have hle : ‖f k (t₀ + s)‖ ≤ 0 := ge_of_tendsto' hlim hbound
  exact norm_le_zero_iff.mp hle

theorem vanish_of_le (f : ℕ → ℝ → ℂ) (B D : ℝ) (hB : 0 ≤ B) (hD : 1 ≤ D)
    (hd : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t)
    (hb : ∀ k t, ‖f k t‖ ≤ B * D ^ k * (k.factorial : ℝ)) (h0 : ∀ k, f k 0 = 0) (m : ℕ) :
    ∀ t : ℝ, |t| ≤ m * (1 / (4 * D)) → ∀ k, f k t = 0 := by
  have hδ : 0 < 1 / (4 * D) := by positivity
  induction m with
  | zero =>
    intro t ht k
    have htz : t = 0 := by
      have : |t| ≤ 0 := by simpa using ht
      exact abs_nonpos_iff.mp this
    rw [htz]
    exact h0 k
  | succ m ih =>
    intro t ht k
    have hm : (0 : ℝ) < m + 1 := by positivity
    push_cast at ht
    have ht0 : |(m : ℝ) / (m + 1) * t| ≤ m * (1 / (4 * D)) := by
      rw [abs_mul, abs_of_nonneg (by positivity), div_mul_eq_mul_div, div_le_iff₀ hm]
      have := mul_le_mul_of_nonneg_left ht (by positivity : (0 : ℝ) ≤ m)
      linarith
    have hs : |t - (m : ℝ) / (m + 1) * t| ≤ 1 / (4 * D) := by
      have he : t - (m : ℝ) / (m + 1) * t = t / (m + 1) := by
        field_simp
        ring
      rw [he, abs_div, abs_of_pos hm, div_le_iff₀ hm]
      linarith
    have h := step f B D hB hD hd hb _ (ih _ ht0) _ hs k
    simpa using h

theorem inner_eq_zero_of_factorial_bounds (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (F : ℕ → ℝ → H) (M C : ℝ) (u : H)
    (hd : ∀ k t, HasDerivAt (F k) (F (k + 1) t) t)
    (hb : ∀ k t, ‖F k t‖ ≤ M * C ^ k * (k.factorial : ℝ))
    (h0 : ∀ k, inner ℂ u (F k 0) = 0) : ∀ t, inner ℂ u (F 0 t) = 0 := by
  intro t
  have hD : 1 ≤ max |C| 1 := le_max_right _ _
  have hM : 0 ≤ M := by
    have := hb 0 0
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one] at this
    exact (norm_nonneg _).trans this
  have hfd : ∀ k t, HasDerivAt (fun t => inner ℂ u (F k t)) (inner ℂ u (F (k + 1) t)) t := by
    intro k t
    have h := ((innerSL ℂ u).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (hd k t)
    simpa [Function.comp_def] using h
  have hfb : ∀ k t, ‖inner ℂ u (F k t)‖ ≤ (‖u‖ * M) * (max |C| 1) ^ k * (k.factorial : ℝ) := by
    intro k t
    have hCk : C ^ k ≤ (max |C| 1) ^ k :=
      (le_abs_self _).trans (by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (le_max_left _ _) k)
    calc ‖inner ℂ u (F k t)‖ ≤ ‖u‖ * ‖F k t‖ := norm_inner_le_norm u (F k t)
      _ ≤ ‖u‖ * (M * C ^ k * k.factorial) := mul_le_mul_of_nonneg_left (hb k t) (norm_nonneg _)
      _ ≤ ‖u‖ * (M * (max |C| 1) ^ k * k.factorial) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCk hM) (Nat.cast_nonneg _))
            (norm_nonneg _)
      _ = (‖u‖ * M) * (max |C| 1) ^ k * k.factorial := by ring
  obtain ⟨m, hm⟩ := exists_nat_ge (|t| * (4 * max |C| 1))
  have ht : |t| ≤ m * (1 / (4 * max |C| 1)) := by
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    exact hm
  exact vanish_of_le (fun k t => inner ℂ u (F k t)) (‖u‖ * M) (max |C| 1) (by positivity) hD hfd hfb
    h0 m t ht 0

end GlobalTheory.CompanionTheory.VectorTaylor
