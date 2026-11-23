import Mathlib
import GroundTheory.AutomorphicForms.DixmierMalliavinLineStage

namespace GroundTheory.Automorphic

open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise FourierTransform

set_option linter.unusedSectionVars false

noncomputable section

namespace LineKernel

theorem tsupport_iteratedDeriv_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (m : ℕ) : tsupport (iteratedDeriv m f) ⊆ tsupport f := by
  induction m with
  | zero => simp
  | succ m ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

theorem iteratedDeriv_eq_of_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : ℕ → ℝ → E} (h : ∀ m, deriv (Φ m) = Φ (m + 1)) (m : ℕ) : iteratedDeriv m (Φ 0) = Φ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [iteratedDeriv_succ, ih, h]

theorem convolution_mul_eq_real (f g : ℝ → ℂ) : (f ⋆[mul ℂ ℂ] g) = (f ⋆[mul ℝ ℂ] g) := by
  funext x; simp only [convolution_def, mul_apply']

theorem iteratedDeriv_convolution {K g : ℝ → ℂ} (hK : LocallyIntegrable K) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (m : ℕ) :
    iteratedDeriv m (K ⋆[mul ℂ ℂ] g) = K ⋆[mul ℂ ℂ] iteratedDeriv m g := by
  have := iteratedDeriv_eq_of_deriv (Φ := fun m => K ⋆[mul ℂ ℂ] iteratedDeriv m g) (fun m => by
    funext x
    rw [convolution_mul_eq_real, convolution_mul_eq_real]
    rw [((hasCompactSupport_iteratedDeriv hgc m).hasDerivAt_convolution_right (mul ℝ ℂ) hK
      ((contDiff_iteratedDeriv_of_contDiff hg m).of_le (by simp)) x).deriv, ← iteratedDeriv_succ]) m
  simpa using this

theorem norm_convolution_le {K g : ℝ → ℂ} {B : ℝ} (hK : Integrable K) (hg : ∀ t, ‖g t‖ ≤ B)
    (x : ℝ) : ‖(K ⋆[mul ℂ ℂ] g) x‖ ≤ B * ∫ t, ‖K t‖ := by
  rw [convolution_mul, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun t => norm_nonneg _) (hK.norm.const_mul B)
    (Eventually.of_forall fun t => ?_))
  simp only [norm_mul]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (hg _) (norm_nonneg _)

section Bounds

variable {a r : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hr : ∀ j, 0 < r j)
include ha hr

theorem integral_norm_KC_le_one (n : ℕ) : ∫ t, ‖KC a r n t‖ ≤ 1 := by
  have : (fun t => ‖KC a r n t‖) = Kc a r n := by
    funext t; simp [KC, Complex.norm_real, abs_of_nonneg (Kc_nonneg ha hr n t)]
  rw [this]; exact integral_Kc_le_one ha hr n

theorem contDiff_ρ (n : ℕ) : ContDiff ℝ ∞ (ρ a r n) := by
  cases n with
  | zero => exact contDiff_ηC a r 0
  | succ n =>
    simp only [ρ]
    exact ContDiff.sum fun p _ => contDiff_const.mul
      (contDiff_iteratedDeriv_of_contDiff (contDiff_conv_ηC ha hr n) p)

theorem support_ρ_subset (n : ℕ) : support (ρ a r n) ⊆ Icc 0 (Rs r n) := by
  cases n with
  | zero =>
    intro t ht
    have : t ∈ Icc (r 0) (2 * r 0) := by
      by_contra h; exact ht (by simp [ρ, ηC, rem_eq_zero (hr 0) h])
    exact ⟨(hr 0).le.trans this.1, by simpa [Rs] using this.2⟩
  | succ n =>
    have hs : tsupport (KC a r n ⋆[mul ℂ ℂ] ηC a r (n + 1)) ⊆ Icc 0 (Rs r (n + 1)) := by
      refine closure_minimal ?_ isClosed_Icc
      refine (support_convolution_subset (mul ℂ ℂ)).trans ?_
      have h1 : support (KC a r n) ⊆ Icc 0 (Rs r n) := fun t ht =>
        support_Kc_subset ha hr n (by simpa [KC] using ht)
      have h2 : support (ηC a r (n + 1)) ⊆ Icc (r (n + 1)) (2 * r (n + 1)) := fun t ht =>
        support_rem_subset (hr (n + 1)) (by simpa [ηC] using ht)
      refine (Set.add_subset_add h1 h2).trans ((Set.Icc_add_Icc_subset _ _ _ _).trans
        (Icc_subset_Icc (by linarith [hr (n + 1)]) (le_of_eq ?_)))
      simp [Rs, Finset.sum_range_succ]
    intro t ht
    by_contra h
    apply ht
    simp only [ρ]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [image_eq_zero_of_notMem_tsupport (fun h' => h (hs (tsupport_iteratedDeriv_subset p h'))),
      mul_zero]

theorem norm_iteratedDeriv_ηC (j q : ℕ) (t : ℝ) :
    ‖iteratedDeriv q (ηC a r j) t‖ = ‖iteratedDeriv q (rem (a j) (r j)) t‖ := by
  have := iteratedDeriv_ofReal (contDiff_rem (a j) (r j)) q
  show ‖iteratedDeriv q (fun t => ((rem (a j) (r j) t : ℝ) : ℂ)) t‖ = _
  rw [this, Complex.norm_real]

theorem norm_iteratedDeriv_ρ_succ_le (n m : ℕ) {B : ℕ → ℝ}
    (hB : ∀ q t, ‖iteratedDeriv q (rem (a (n + 1)) (r (n + 1))) t‖ ≤ B q) (t : ℝ) :
    ‖iteratedDeriv m (ρ a r (n + 1)) t‖ ≤
      ∑ p ∈ Finset.range (n + 2), coef a (n + 1) p * B (p + m) := by
  have hKi := (integrable_KC ha hr n).locallyIntegrable
  have hηc := contDiff_ηC a r (n + 1)
  have hηs := hasCompactSupport_ηC ha hr (n + 1)
  set Φ : ℕ → ℝ → ℂ := fun m u => ∑ p ∈ Finset.range (n + 2),
    (coef a (n + 1) p : ℂ) * (KC a r n ⋆[mul ℂ ℂ] iteratedDeriv (p + m) (ηC a r (n + 1))) u
    with hΦ
  have h0 : ρ a r (n + 1) = Φ 0 := by
    funext u
    simp only [ρ, hΦ, add_zero, iteratedDeriv_convolution hKi hηc hηs]
  have hd : ∀ m, deriv (Φ m) = Φ (m + 1) := by
    intro m; funext x
    have hsum := HasDerivAt.sum (u := Finset.range (n + 2))
      (A := fun p u => (coef a (n + 1) p : ℂ) *
        (KC a r n ⋆[mul ℂ ℂ] iteratedDeriv (p + m) (ηC a r (n + 1))) u)
      (A' := fun p => (coef a (n + 1) p : ℂ) *
        (KC a r n ⋆[mul ℂ ℂ] iteratedDeriv (p + m + 1) (ηC a r (n + 1))) x) (x := x)
      (fun p _ => by
        refine HasDerivAt.const_mul _ ?_
        rw [convolution_mul_eq_real, convolution_mul_eq_real, iteratedDeriv_succ]
        exact (hasCompactSupport_iteratedDeriv hηs (p + m)).hasDerivAt_convolution_right
          (mul ℝ ℂ) hKi ((contDiff_iteratedDeriv_of_contDiff hηc _).of_le (by simp)) x)
    have e : Φ m = ∑ p ∈ Finset.range (n + 2), fun u => (coef a (n + 1) p : ℂ) *
        (KC a r n ⋆[mul ℂ ℂ] iteratedDeriv (p + m) (ηC a r (n + 1))) u := by
      funext u; simp [hΦ, Finset.sum_apply]
    rw [e, hsum.deriv]
    simp only [hΦ, add_assoc]
  rw [h0, iteratedDeriv_eq_of_deriv hd m]
  simp only [hΦ]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (coef_nonneg ha _ _)]
  refine mul_le_mul_of_nonneg_left ?_ (coef_nonneg ha _ _)
  have hB' : ∀ u, ‖iteratedDeriv (p + m) (ηC a r (n + 1)) u‖ ≤ B (p + m) := fun u => by
    rw [norm_iteratedDeriv_ηC ha hr]; exact hB _ _
  refine (norm_convolution_le (integrable_KC ha hr n) hB' t).trans ?_
  have h1 := integral_norm_KC_le_one ha hr n
  have h2 : 0 ≤ B (p + m) := (norm_nonneg _).trans (hB (p + m) 0)
  have h3 : 0 ≤ ∫ t, ‖KC a r n t‖ := integral_nonneg fun t => norm_nonneg _
  nlinarith

theorem fourier_KC_zero (ξ : ℝ) : 𝓕 (KC a r 0) ξ = khat (a 0) (r 0) ξ := rfl

theorem fourier_KC_succ (n : ℕ) (ξ : ℝ) :
    𝓕 (KC a r (n + 1)) ξ = 𝓕 (KC a r n) ξ * khat (a (n + 1)) (r (n + 1)) ξ := by
  rw [KC_succ ha hr n, fourier_mul_convolution_eq (f₂ := kC a r (n + 1)) (integrable_KC ha hr n)
    (integrable_kern (ha (n + 1)).le (hr (n + 1))).ofReal]
  rfl

theorem norm_fourier_KC_le_one (n : ℕ) (ξ : ℝ) : ‖𝓕 (KC a r n) ξ‖ ≤ 1 := by
  induction n with
  | zero => rw [fourier_KC_zero ha hr]; exact norm_khat_le_one (ha 0) (hr 0) ξ
  | succ n ih =>
    rw [fourier_KC_succ ha hr, norm_mul]
    exact mul_le_one₀ ih (norm_nonneg _) (norm_khat_le_one (ha _) (hr _) ξ)

theorem norm_fourier_KC_succ_sub_le (n : ℕ) (ξ : ℝ) :
    ‖𝓕 (KC a r (n + 1)) ξ - 𝓕 (KC a r n) ξ‖ ≤
      4 * π * r (n + 1) * |ξ| + exp (-a (n + 1) * r (n + 1)) := by
  rw [fourier_KC_succ ha hr, ← mul_sub_one, norm_mul]
  calc ‖𝓕 (KC a r n) ξ‖ * ‖khat (a (n + 1)) (r (n + 1)) ξ - 1‖
      ≤ 1 * (4 * π * r (n + 1) * |ξ| + exp (-a (n + 1) * r (n + 1))) :=
        mul_le_mul (norm_fourier_KC_le_one ha hr n ξ) (norm_khat_sub_one_le (ha _) (hr _) ξ)
          (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem abs_pow_mul_norm_fourier_KC_le (n m : ℕ) (hmn : m ≤ n + 1) (ξ : ℝ) :
    |ξ| ^ m * ‖𝓕 (KC a r n) ξ‖ ≤ ∏ j ∈ Finset.range m, (a j / π) := by
  induction n generalizing m with
  | zero =>
    interval_cases m
    · simpa using norm_fourier_KC_le_one ha hr 0 ξ
    · simpa [fourier_KC_zero ha hr] using abs_mul_norm_khat_le (ha 0) (hr 0) ξ
  | succ n ih =>
    rw [fourier_KC_succ ha hr, norm_mul]
    rcases Nat.lt_or_ge m (n + 2) with h | h
    · calc |ξ| ^ m * (‖𝓕 (KC a r n) ξ‖ * ‖khat (a (n + 1)) (r (n + 1)) ξ‖)
          ≤ |ξ| ^ m * (‖𝓕 (KC a r n) ξ‖ * 1) := by
            gcongr; exact norm_khat_le_one (ha _) (hr _) ξ
        _ ≤ _ := by rw [mul_one]; exact ih m (by omega)
    · obtain rfl : m = n + 2 := le_antisymm hmn h
      rw [Finset.prod_range_succ, pow_succ]
      calc |ξ| ^ (n + 1) * |ξ| * (‖𝓕 (KC a r n) ξ‖ * ‖khat (a (n + 1)) (r (n + 1)) ξ‖)
          = (|ξ| ^ (n + 1) * ‖𝓕 (KC a r n) ξ‖) * (|ξ| * ‖khat (a (n + 1)) (r (n + 1)) ξ‖) := by
            ring
        _ ≤ (∏ j ∈ Finset.range (n + 1), (a j / π)) * (a (n + 1) / π) :=
            mul_le_mul (ih (n + 1) le_rfl) (abs_mul_norm_khat_le (ha _) (hr _) ξ)
              (by positivity) (Finset.prod_nonneg fun j _ => div_nonneg (ha j).le pi_pos.le)

end Bounds

theorem coef_mono {a : ℕ → ℝ} (ha : ∀ j, 0 < a j) (n p : ℕ) : coef a n p ≤ coef a (n + 1) p := by
  cases p with
  | zero => simp [coef]
  | succ p => simp only [coef]; linarith [div_nonneg (coef_nonneg ha n p) (ha n).le]

theorem coef_le_of {a β : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hβ0 : β 0 = 1) (hβp : ∀ p, 0 ≤ β p)
    (hβ : ∀ n p, 1 ≤ p → p ≤ n + 1 → (a n)⁻¹ * β (p - 1) ≤ (1 / 2) ^ (n + 1) * β p)
    (n p : ℕ) : coef a n p ≤ β p := by
  have key : ∀ n p, 1 ≤ p → coef a n p ≤ β p * (1 - (1 / 2) ^ n) := by
    intro n
    induction n with
    | zero =>
      intro p hp
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      simp [coef]
    | succ n ih =>
      intro p hp
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      simp only [coef]
      have h1 := ih (q + 1) (by omega)
      have h2 : coef a n q / a n ≤ (1 / 2) ^ (n + 1) * β (q + 1) := by
        rcases Nat.lt_or_ge n q with hq | hq
        · rw [coef_eq_zero a hq, zero_div]
          have := hβ n (q + 1) (by omega)
          have hb : 0 ≤ β (q + 1) := hβp _
          positivity
        · have hc : coef a n q ≤ β q := by
            rcases Nat.eq_zero_or_pos q with rfl | hq0
            · rw [coef_zero_right, hβ0]
            · have := ih q hq0
              have hbq : 0 ≤ β q := hβp q
              nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n]
          have := hβ n (q + 1) (by omega) (by omega)
          simp only [Nat.add_sub_cancel] at this
          calc coef a n q / a n = (a n)⁻¹ * coef a n q := by ring
            _ ≤ (a n)⁻¹ * β q := mul_le_mul_of_nonneg_left hc (inv_nonneg.2 (ha n).le)
            _ ≤ _ := this
      calc coef a n (q + 1) + coef a n q / a n
          ≤ β (q + 1) * (1 - (1 / 2) ^ n) + (1 / 2) ^ (n + 1) * β (q + 1) := add_le_add h1 h2
        _ = β (q + 1) * (1 - (1 / 2) ^ (n + 1)) := by ring
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · rw [coef_zero_right, hβ0]
  · have := key n p hp
    nlinarith [hβp p, pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n]

end LineKernel

end

end GroundTheory.Automorphic
