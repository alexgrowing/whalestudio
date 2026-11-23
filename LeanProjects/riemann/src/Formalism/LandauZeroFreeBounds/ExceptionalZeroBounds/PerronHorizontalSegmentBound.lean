import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf

open Complex MeasureTheory

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem norm_perron_integrand_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (y : ℝ) (hy : 0 < y) (w : ℂ) :
    ‖Fchi χ y w‖ = ‖negLD χ w‖ * y ^ w.re / (‖w‖ * ‖w - 1‖) := by
  unfold Fchi
  rw [norm_div, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]

theorem norm_sum_le_of_card_le_one (B : Finset ℝ) (hB : B.card ≤ 1) (f : ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ β ∈ B, ‖f β‖ ≤ M) : ‖∑ β ∈ B, f β‖ ≤ M := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hB with h | h
  · rw [Finset.card_eq_zero.mp h]; simpa using hM
  · obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp h
    simpa using hf b (Finset.mem_singleton_self b)

theorem perron_right_line_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (C₀ : ℝ)
    (hR : ∀ s : ℂ, 1 < s.re → ‖negLD χ s‖ ≤ 1 / (s.re - 1) + C₀)
    (y T t : ℝ) (hy : 1 < y) (hT : 0 < T) (ht : T ≤ |t|) :
    ‖Fchi χ y (((1 + 1 / Real.log y : ℝ) : ℂ) + t * I)‖ ≤
      (Real.log y + C₀) * (Real.exp 1 * y) / t ^ 2 := by
  have hL0 : 0 < Real.log y := Real.log_pos hy
  have hy0 : 0 < y := by linarith
  set L := Real.log y with hL
  set w : ℂ := ((1 + 1 / L : ℝ) : ℂ) + t * I with hw
  have hwre : w.re = 1 + 1 / L := by simp [hw]
  have hwim : w.im = t := by simp [hw]
  have ht0 : 0 < |t| := lt_of_lt_of_le hT ht
  rw [norm_perron_integrand_eq χ y hy0 w, hwre]
  have hN : ‖negLD χ w‖ ≤ L + C₀ := by
    have hpos : 0 < 1 / L := by positivity
    have h1 := hR w (by rw [hwre]; linarith)
    rw [hwre] at h1
    simpa [one_div, inv_inv] using h1
  have hpow : y ^ (1 + 1 / L) = Real.exp 1 * y := by
    rw [Real.rpow_def_of_pos hy0, ← hL, mul_add, mul_one, mul_one_div_cancel hL0.ne',
      Real.exp_add, Real.exp_log hy0]
    ring
  have hw1 : |t| ≤ ‖w‖ := by rw [← hwim]; exact Complex.abs_im_le_norm w
  have hw2 : |t| ≤ ‖w - 1‖ := by
    have h2 : (w - 1).im = t := by simp [hwim]
    rw [← h2]; exact Complex.abs_im_le_norm _
  rw [hpow]
  have htt : t ^ 2 ≤ ‖w‖ * ‖w - 1‖ := by
    rw [← sq_abs]; nlinarith [abs_nonneg t]
  have htt0 : 0 < t ^ 2 := by rw [← sq_abs]; positivity
  have hNn : 0 ≤ L + C₀ := le_trans (norm_nonneg _) hN
  have hey : 0 < Real.exp 1 * y := by positivity
  calc ‖negLD χ w‖ * (Real.exp 1 * y) / (‖w‖ * ‖w - 1‖)
      ≤ (L + C₀) * (Real.exp 1 * y) / (‖w‖ * ‖w - 1‖) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hN hey.le) (by positivity)
    _ ≤ (L + C₀) * (Real.exp 1 * y) / t ^ 2 :=
        div_le_div_of_nonneg_left (mul_nonneg hNn hey.le) htt0 htt

theorem log_conductor_pos_real (q : ℕ) [NeZero q] (u : ℝ) : 0 < Real.log ((q : ℝ) * (|u| + 2)) := by
  apply Real.log_pos
  have hq : (1:ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  nlinarith [abs_nonneg u]

theorem log_analytic_conductor_mono (q : ℕ) [NeZero q] (u T : ℝ) (hu : |u| ≤ T) :
    Real.log ((q : ℝ) * (|u| + 2)) ≤ Real.log ((q : ℝ) * (T + 2)) := by
  have hq : (1:ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  apply Real.log_le_log
  · nlinarith [abs_nonneg u]
  · exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)

theorem perron_horizontal_segment_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (c₁ C : ℝ)
    (B : Finset ℝ) (hB : B.card ≤ 1)
    (hD : ∀ s : ℂ, InRegion (c₁ / 2) q s → (∀ β ∈ B, s ≠ (β : ℂ)) →
        ‖negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤ C * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2)
    (y T x v σ₀ σ₁ : ℝ) (hy : 1 ≤ y) (hT : 1 ≤ T) (hv : |v| = T)
    (hσ₁ : 1 - (c₁ / 2) / Real.log ((q : ℝ) * (T + 2)) ≤ σ₁)
    (hx1 : σ₁ ≤ x) (hx2 : x ≤ σ₀) :
    ‖Fchi χ y ((x : ℂ) + (v : ℂ) * I)‖ ≤
      (C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1) * y ^ σ₀ / T ^ 2 := by
  have hy0 : 0 < y := by linarith
  have hT0 : 0 < T := by linarith
  set s : ℂ := (x : ℂ) + (v : ℂ) * I with hs
  have hsre : s.re = x := by simp [hs]
  have hsim : s.im = v := by simp [hs]
  have hreg : InRegion (c₁ / 2) q s := by
    unfold InRegion; rw [hsim, hsre, hv]; exact le_trans hσ₁ hx1
  have hne : ∀ β ∈ B, s ≠ (β : ℂ) := by
    intro β _ h
    have h1 := congrArg Complex.im h
    rw [hsim, Complex.ofReal_im] at h1
    rw [h1] at hv; simp at hv; linarith
  have hsum : ‖∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤ 1 := by
    refine norm_sum_le_of_card_le_one B hB (fun β : ℝ => 1 / (s - (β : ℂ))) 1 zero_le_one ?_
    intro β _
    rw [norm_div, norm_one]
    have h2 : (s - (β : ℂ)).im = v := by simp [hsim]
    have h1 : (1:ℝ) ≤ ‖s - (β : ℂ)‖ := by
      calc (1:ℝ) ≤ T := hT
        _ = |v| := hv.symm
        _ = |(s - (β : ℂ)).im| := by rw [h2]
        _ ≤ ‖s - (β : ℂ)‖ := Complex.abs_im_le_norm _
    rw [div_le_one (by linarith)]; exact h1
  have hD' := hD s hreg hne
  rw [hsim, hv] at hD'
  have hN : ‖negLD χ s‖ ≤ C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1 := by
    have h3 := norm_sub_le (negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))) (∑ β ∈ B, 1 / (s - (β : ℂ)))
    rw [add_sub_cancel_right] at h3
    linarith
  rw [norm_perron_integrand_eq χ y hy0 s, hsre]
  have hK : 0 ≤ C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1 := le_trans (norm_nonneg _) hN
  have hyx : y ^ x ≤ y ^ σ₀ := Real.rpow_le_rpow_of_exponent_le hy hx2
  have hw1 : T ≤ ‖s‖ := by rw [← hv, ← hsim]; exact Complex.abs_im_le_norm s
  have hw2 : T ≤ ‖s - 1‖ := by
    have h4 : (s - 1).im = v := by simp [hsim]
    rw [← hv, ← h4]; exact Complex.abs_im_le_norm _
  have hden : T ^ 2 ≤ ‖s‖ * ‖s - 1‖ := by nlinarith
  calc ‖negLD χ s‖ * y ^ x / (‖s‖ * ‖s - 1‖)
      ≤ (C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1) * y ^ σ₀ / (‖s‖ * ‖s - 1‖) :=
        div_le_div_of_nonneg_right (mul_le_mul hN hyx (by positivity) hK) (by positivity)
    _ ≤ (C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1) * y ^ σ₀ / T ^ 2 :=
        div_le_div_of_nonneg_left (mul_nonneg hK (Real.rpow_nonneg hy0.le _)) (by positivity) hden

theorem perron_left_line_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (c₁ C : ℝ)
    (hc₁ : 0 ≤ c₁) (hC : 0 ≤ C) (B : Finset ℝ) (hB : B.card ≤ 1)
    (hD : ∀ s : ℂ, InRegion (c₁ / 2) q s → (∀ β ∈ B, s ≠ (β : ℂ)) →
        ‖negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤ C * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2)
    (y T u σ₁ δ ε : ℝ) (hy : 0 < y) (hu : |u| ≤ T)
    (hσ₁ : 1 - (c₁ / 2) / Real.log ((q : ℝ) * (T + 2)) ≤ σ₁) (hhalf : 1 / 2 ≤ σ₁)
    (hε : 0 < ε) (hgap : ε ≤ 1 - σ₁) (hδ : 0 < δ) (hδB : ∀ β ∈ B, δ ≤ |σ₁ - β|) :
    ‖Fchi χ y ((σ₁ : ℂ) + u * I)‖ ≤
      (C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1 / δ) * y ^ σ₁ * (2 / ε) := by
  set s : ℂ := (σ₁ : ℂ) + (u : ℂ) * I with hs
  have hsre : s.re = σ₁ := by simp [hs]
  have hsim : s.im = u := by simp [hs]
  have hLu := log_conductor_pos_real q u
  have hmono := log_analytic_conductor_mono q u T hu
  have hreg : InRegion (c₁ / 2) q s := by
    unfold InRegion; rw [hsim, hsre]
    refine le_trans ?_ hσ₁
    have h1 : (c₁ / 2) / Real.log ((q : ℝ) * (T + 2)) ≤ (c₁ / 2) / Real.log ((q : ℝ) * (|u| + 2)) :=
      div_le_div_of_nonneg_left (by linarith) hLu hmono
    linarith
  have hdist : ∀ β ∈ B, δ ≤ ‖s - (β : ℂ)‖ := by
    intro β hβ
    have h1 : (s - (β : ℂ)).re = σ₁ - β := by simp [hsre]
    calc δ ≤ |σ₁ - β| := hδB β hβ
      _ = |(s - (β : ℂ)).re| := by rw [h1]
      _ ≤ ‖s - (β : ℂ)‖ := Complex.abs_re_le_norm _
  have hne : ∀ β ∈ B, s ≠ (β : ℂ) := by
    intro β hβ h
    have h1 := hdist β hβ
    rw [h, sub_self, norm_zero] at h1; linarith
  have hsum : ‖∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤ 1 / δ := by
    refine norm_sum_le_of_card_le_one B hB (fun β : ℝ => 1 / (s - (β : ℂ))) (1 / δ) (by positivity) ?_
    intro β hβ
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hδ (hdist β hβ)
  have hD' := hD s hreg hne
  rw [hsim] at hD'
  have hlogsq : Real.log ((q : ℝ) * (|u| + 2)) ^ 2 ≤ Real.log ((q : ℝ) * (T + 2)) ^ 2 :=
    pow_le_pow_left₀ hLu.le hmono 2
  have hN : ‖negLD χ s‖ ≤ C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1 / δ := by
    have h3 := norm_sub_le (negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))) (∑ β ∈ B, 1 / (s - (β : ℂ)))
    rw [add_sub_cancel_right] at h3
    have h4 : C * Real.log ((q : ℝ) * (|u| + 2)) ^ 2 ≤ C * Real.log ((q : ℝ) * (T + 2)) ^ 2 :=
      mul_le_mul_of_nonneg_left hlogsq hC
    linarith
  have hK : 0 ≤ C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1 / δ := le_trans (norm_nonneg _) hN
  rw [norm_perron_integrand_eq χ y hy s, hsre]
  have hw1 : 1 / 2 ≤ ‖s‖ := by
    calc (1:ℝ) / 2 ≤ σ₁ := hhalf
      _ ≤ |σ₁| := le_abs_self _
      _ = |s.re| := by rw [hsre]
      _ ≤ ‖s‖ := Complex.abs_re_le_norm s
  have hw2 : ε ≤ ‖s - 1‖ := by
    have h5 : (s - 1).re = σ₁ - 1 := by simp [hsre]
    calc ε ≤ 1 - σ₁ := hgap
      _ ≤ |σ₁ - 1| := by rw [abs_sub_comm]; exact le_abs_self _
      _ = |(s - 1).re| := by rw [h5]
      _ ≤ ‖s - 1‖ := Complex.abs_re_le_norm _
  have hden : ε / 2 ≤ ‖s‖ * ‖s - 1‖ := by nlinarith
  have hden0 : 0 < ‖s‖ * ‖s - 1‖ := by linarith
  have hyp : 0 < y ^ σ₁ := Real.rpow_pos_of_pos hy _
  have h2 : (2 / ε) * (ε / 2) = 1 := by field_simp
  rw [div_le_iff₀ hden0]
  calc ‖negLD χ s‖ * y ^ σ₁ ≤ (C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1 / δ) * y ^ σ₁ :=
        mul_le_mul_of_nonneg_right hN hyp.le
    _ = (C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1 / δ) * y ^ σ₁ * (2 / ε) * (ε / 2) := by
        rw [mul_assoc _ (2 / ε), h2, mul_one]
    _ ≤ (C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1 / δ) * y ^ σ₁ * (2 / ε) * (‖s‖ * ‖s - 1‖) :=
        mul_le_mul_of_nonneg_left hden (mul_nonneg (mul_nonneg hK hyp.le) (by positivity))

theorem real_zero_residue_term_bound (y β σ₁ ε : ℝ) (hy : 1 ≤ y) (hβ : 1 / 2 ≤ β) (hβσ : β ≤ σ₁) (hε : 0 < ε)
    (hgap : ε ≤ 1 - σ₁) :
    ‖(y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1))‖ ≤ y ^ σ₁ * (2 / ε) := by
  have hy0 : 0 < y := by linarith
  have hβ1 : β < 1 := by linarith
  have hnum : ‖(y : ℂ) ^ (β : ℂ)‖ = y ^ β := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0]; simp
  have hden : ‖(β : ℂ) * ((β : ℂ) - 1)‖ = β * (1 - β) := by
    rw [norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith), abs_of_neg (by linarith)]
    ring
  rw [norm_div, hnum, hden]
  have hyb : y ^ β ≤ y ^ σ₁ := Real.rpow_le_rpow_of_exponent_le hy hβσ
  have hd : ε / 2 ≤ β * (1 - β) := by
    nlinarith [mul_le_mul_of_nonneg_right hβ (by linarith : (0:ℝ) ≤ 1 - β)]
  have hyp : 0 < y ^ σ₁ := Real.rpow_pos_of_pos hy0 _
  have h2 : (2 / ε) * (ε / 2) = 1 := by field_simp
  rw [div_le_iff₀ (by linarith)]
  calc y ^ β ≤ y ^ σ₁ := hyb
    _ = y ^ σ₁ * (2 / ε) * (ε / 2) := by rw [mul_assoc _ (2 / ε), h2, mul_one]
    _ ≤ y ^ σ₁ * (2 / ε) * (β * (1 - β)) :=
        mul_le_mul_of_nonneg_left hd (mul_nonneg hyp.le (by positivity))

end Formalism.ZeroFreeDirichlet
