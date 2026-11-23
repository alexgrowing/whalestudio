import Mathlib
import GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoSeries
import GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoStep
import GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoGarding

namespace GroundTheory.Automorphic.Sobolev

open MeasureTheory Finset
open scoped ContDiff

noncomputable section

variable {n : ℕ}

theorem powMul_self_le {s i q : ℕ} (h : i + q ≤ s) : (s : ℝ) ^ i * (q : ℝ) ^ q ≤ (s : ℝ) ^ s := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · obtain ⟨rfl, rfl⟩ : i = 0 ∧ q = 0 := by omega
    simp
  · have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
    calc (s : ℝ) ^ i * (q : ℝ) ^ q ≤ (s : ℝ) ^ i * (s : ℝ) ^ q := by
          gcongr; exact_mod_cast (by omega : q ≤ s)
      _ = (s : ℝ) ^ (i + q) := by rw [pow_add]
      _ ≤ (s : ℝ) ^ s := pow_le_pow_right₀ hs' h

theorem pow_self_le_exp_mul_factorial (p : ℕ) :
    (p : ℝ) ^ p ≤ Real.exp 1 ^ p * p.factorial := by
  have h := Real.pow_div_factorial_le_exp (x := (p : ℝ)) (Nat.cast_nonneg _) p
  rw [div_le_iff₀ (by positivity), ← Real.exp_one_pow] at h
  exact h

theorem factorial_add_le (k σ : ℕ) :
    ((k + σ).factorial : ℝ) ≤ 2 ^ (k + σ) * k.factorial * σ.factorial := by
  have h := Nat.add_choose_mul_factorial_mul_factorial k σ
  have hc : (k + σ).choose σ ≤ 2 ^ (k + σ) := Nat.choose_le_two_pow _ _
  have : (k + σ).factorial ≤ 2 ^ (k + σ) * k.factorial * σ.factorial := by
    rw [← h]
    gcongr
  exact_mod_cast this

theorem l2Norm_sqrt_sum_derivative_cutoff_power_le {u : EuclideanSpace ℝ (Fin n) → ℂ} (hu : ContDiff ℝ ∞ u)
    (hu_c : HasCompactSupport u) {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (h01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) {K : ℝ} (hK0 : 0 ≤ K) {L₀ : ℕ}
    (hK : ∀ (s i : ℕ) (x : EuclideanSpace ℝ (Fin n)), i ≤ L₀ → i ≤ s →
      hsD i (fun y ↦ ((χ y : ℂ)) ^ s) x ≤ K * (s : ℝ) ^ i * χ x ^ (s - i))
    {k s j : ℕ} (hjL : j ≤ L₀) (hjs : j + k ≤ s) :
    l2n (fun x ↦ Real.sqrt (∑ I : Fin k → Fin n,
        hsD j (fun y ↦ ((χ y : ℂ)) ^ s * pdT I u y) x ^ 2)) ≤
      ∑ ij ∈ antidiagonal j, (j.choose ij.1 : ℝ) * (K * (s : ℝ) ^ ij.1) * wN χ u (ij.2 + k) := by
  have mem : ∀ {f : EuclideanSpace ℝ (Fin n) → ℝ}, Continuous f →
      (∀ x, x ∉ tsupport u → f x = 0) → MemLp f 2 volume := fun hc hz ↦
    memLp_two_of_continuous_hasCompactSupport hc (HasCompactSupport.intro hu_c hz)
  have memg : ∀ q, MemLp (fun x ↦ χ x ^ q * hsD q u x) 2 volume := fun q ↦
    mem ((hχ.continuous.pow q).mul (continuous_hsD hu q)) fun x hx ↦ by
      rw [hsD_eq_zero_of_eventuallyEq_zero (notMem_tsupport_iff_eventuallyEq.1 hx), mul_zero]
  have memR : MemLp (fun x ↦ ∑ ij ∈ antidiagonal j, (j.choose ij.1 : ℝ) * (K * (s : ℝ) ^ ij.1) *
      (χ x ^ (ij.2 + k) * hsD (ij.2 + k) u x)) 2 volume :=
    memLp_sum_mul _ _ _ fun ij _ ↦ memg _
  have hvC : ∀ I : Fin k → Fin n, ContDiff ℝ ∞ (fun y ↦ ((χ y : ℂ)) ^ s * pdT I u y) :=
    fun I ↦ (contDiff_weight hχ s).mul (contDiff_pdT hu I)
  have hcont : Continuous (fun x ↦ Real.sqrt (∑ I : Fin k → Fin n,
      hsD j (fun y ↦ ((χ y : ℂ)) ^ s * pdT I u y) x ^ 2)) :=
    (continuous_finsetSum _ fun I _ ↦ (continuous_hsD (hvC I) j).pow 2).sqrt
  refine (l2Norm_le_of_abs_le memR hcont.aestronglyMeasurable fun x ↦ ?_).trans
    (l2Norm_sum_const_mul_le _ _ (fun _ _ ↦ by positivity) _ fun ij _ ↦ memg _)
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  exact sqrt_sum_hsD_weight_le hu hχ h01 hK0 hK hjL hjs x

theorem hsD_le_of_sobolev {u : EuclideanSpace ℝ (Fin n) → ℂ} (hu : ContDiff ℝ ∞ u)
    (hu_c : HasCompactSupport u) {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (h01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) {K : ℝ} (hK0 : 0 ≤ K) {L₀ : ℕ}
    (hK : ∀ (s i : ℕ) (x : EuclideanSpace ℝ (Fin n)), i ≤ L₀ → i ≤ s →
      hsD i (fun y ↦ ((χ y : ℂ)) ^ s) x ≤ K * (s : ℝ) ^ i * χ x ^ (s - i))
    {σ : ℕ} (hσL : σ ≤ L₀) {CS : ℝ} (hCS : 0 ≤ CS)
    (hsob : ∀ w : EuclideanSpace ℝ (Fin n) → ℂ, ContDiff ℝ ∞ w → HasCompactSupport w →
      ∀ x, ‖w x‖ ≤ CS * (l2n (hsD 0 w) + l2n (hsD σ w)))
    (k : ℕ) {y : EuclideanSpace ℝ (Fin n)} (hy : χ y = 1) :
    hsD k u y ≤ CS * ((∑ ij ∈ antidiagonal 0, (Nat.choose 0 ij.1 : ℝ) *
        (K * ((k + σ : ℕ) : ℝ) ^ ij.1) * wN χ u (ij.2 + k)) +
      ∑ ij ∈ antidiagonal σ, (σ.choose ij.1 : ℝ) * (K * ((k + σ : ℕ) : ℝ) ^ ij.1) *
        wN χ u (ij.2 + k)) := by
  set s := k + σ with hs
  set w : (Fin k → Fin n) → EuclideanSpace ℝ (Fin n) → ℂ :=
    fun I z ↦ ((χ z : ℂ)) ^ s * pdT I u z with hw
  have hwC : ∀ I, ContDiff ℝ ∞ (w I) := fun I ↦ (contDiff_weight hχ s).mul (contDiff_pdT hu I)
  have hwc : ∀ I, HasCompactSupport (w I) := by
    intro I
    refine HasCompactSupport.intro hu_c fun x hx ↦ ?_
    have := (dT_eventuallyEq_zero_of_not_mem_tsupport hx (fun l ↦ ev (I l))).self_of_nhds
    simp only [hw, pdT]
    rw [this, mul_zero]
  have mem : ∀ {f : EuclideanSpace ℝ (Fin n) → ℝ}, Continuous f →
      (∀ x, x ∉ tsupport u → f x = 0) → MemLp f 2 volume := fun hc hz ↦
    memLp_two_of_continuous_hasCompactSupport hc (HasCompactSupport.intro hu_c hz)
  have memh : ∀ j I, MemLp (hsD j (w I)) 2 volume := fun j I ↦
    memLp_two_of_continuous_hasCompactSupport (continuous_hsD (hwC I) j) (by
      refine HasCompactSupport.intro (hwc I) fun x hx ↦ ?_
      exact hsD_eq_zero_of_eventuallyEq_zero (notMem_tsupport_iff_eventuallyEq.1 hx) j)
  have hpt : ∀ I, ‖pdT I u y‖ ≤ CS * (l2n (hsD 0 (w I)) + l2n (hsD σ (w I))) := by
    intro I
    have h := hsob (w I) (hwC I) (hwc I) y
    simp only [hw, hy, Complex.ofReal_one, one_pow, one_mul] at h
    exact h
  have e0 : l2n (fun x ↦ Real.sqrt (∑ I : Fin k → Fin n, hsD 0 (w I) x ^ 2)) =
      Real.sqrt (∑ I : Fin k → Fin n, l2n (hsD 0 (w I)) ^ 2) :=
    l2Norm_sqrt_sum_sq_eq _ fun I ↦ memh 0 I
  have eσ : l2n (fun x ↦ Real.sqrt (∑ I : Fin k → Fin n, hsD σ (w I) x ^ 2)) =
      Real.sqrt (∑ I : Fin k → Fin n, l2n (hsD σ (w I)) ^ 2) :=
    l2Norm_sqrt_sum_sq_eq _ fun I ↦ memh σ I
  have h0 := l2Norm_sqrt_sum_derivative_cutoff_power_le hu hu_c hχ h01 hK0 hK (k := k) (s := s) (j := 0)
    (Nat.zero_le _) (by omega)
  have hσ := l2Norm_sqrt_sum_derivative_cutoff_power_le hu hu_c hχ h01 hK0 hK (k := k) (s := s) (j := σ)
    hσL (by omega)
  calc hsD k u y = Real.sqrt (∑ I : Fin k → Fin n, ‖pdT I u y‖ ^ 2) := rfl
    _ ≤ Real.sqrt (∑ I : Fin k → Fin n,
          (CS * (l2n (hsD 0 (w I)) + l2n (hsD σ (w I)))) ^ 2) :=
        sqrt_sum_sq_mono fun I ↦ ⟨norm_nonneg _, hpt I⟩
    _ = CS * Real.sqrt (∑ I : Fin k → Fin n, (l2n (hsD 0 (w I)) + l2n (hsD σ (w I))) ^ 2) := by
        rw [sqrt_sum_sq_const_mul, abs_of_nonneg hCS]
    _ ≤ CS * (Real.sqrt (∑ I : Fin k → Fin n, l2n (hsD 0 (w I)) ^ 2) +
          Real.sqrt (∑ I : Fin k → Fin n, l2n (hsD σ (w I)) ^ 2)) :=
        mul_le_mul_of_nonneg_left (sqrt_sum_sq_add_le _ _) hCS
    _ ≤ _ := by
        rw [← e0, ← eσ]
        exact mul_le_mul_of_nonneg_left (add_le_add h0 hσ) hCS

theorem exists_norm_iteratedFDeriv_le_of_wN {u : EuclideanSpace ℝ (Fin n) → ℂ}
    (hu : ContDiff ℝ ∞ u) (hu_c : HasCompactSupport u) {χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (h01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) {K : ℝ} (hK0 : 0 ≤ K) {L₀ : ℕ}
    (hK : ∀ (s i : ℕ) (x : EuclideanSpace ℝ (Fin n)), i ≤ L₀ → i ≤ s →
      hsD i (fun y ↦ ((χ y : ℂ)) ^ s) x ≤ K * (s : ℝ) ^ i * χ x ^ (s - i))
    {σ : ℕ} (hσL : σ ≤ L₀) {CS : ℝ} (hCS : 0 ≤ CS)
    (hsob : ∀ w : EuclideanSpace ℝ (Fin n) → ℂ, ContDiff ℝ ∞ w → HasCompactSupport w →
      ∀ x, ‖w x‖ ≤ CS * (l2n (hsD 0 w) + l2n (hsD σ w)))
    {B L : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) (hN : ∀ p : ℕ, wN χ u p ≤ B * L ^ p * (p : ℝ) ^ p) :
    ∃ C M : ℝ, ∀ (k : ℕ) (y : EuclideanSpace ℝ (Fin n)), χ y = 1 →
      ‖iteratedFDeriv ℝ k u y‖ ≤ C * M ^ k * k.factorial := by
  set e := Real.exp 1
  have he : 0 ≤ e := (Real.exp_pos 1).le
  refine ⟨CS * (2 * 2 ^ σ * K * B) * (σ.factorial * (2 * e * L) ^ σ), 2 * e * L, fun k y hy ↦ ?_⟩
  set s := k + σ with hs
  have hL0 : 0 ≤ L := by linarith

  have hterm : ∀ j, j ≤ σ → ∑ ij ∈ antidiagonal j, (j.choose ij.1 : ℝ) *
      (K * ((k + σ : ℕ) : ℝ) ^ ij.1) * wN χ u (ij.2 + k) ≤ 2 ^ σ * K * (B * L ^ s * (s : ℝ) ^ s) := by
    intro j hj
    calc ∑ ij ∈ antidiagonal j, (j.choose ij.1 : ℝ) * (K * ((k + σ : ℕ) : ℝ) ^ ij.1) *
          wN χ u (ij.2 + k)
        ≤ ∑ ij ∈ antidiagonal j, (j.choose ij.1 : ℝ) * K * (B * L ^ s * (s : ℝ) ^ s) := by
          refine Finset.sum_le_sum fun ij hij ↦ ?_
          have h1 : ij.1 + ij.2 = j := mem_antidiagonal.1 hij
          have hb := hN (ij.2 + k)
          have hp := powMul_self_le (s := s) (i := ij.1) (q := ij.2 + k) (by omega)
          have hLq : L ^ (ij.2 + k) ≤ L ^ s := pow_le_pow_right₀ hL (by omega)
          have hsi : (0 : ℝ) ≤ (s : ℝ) ^ ij.1 := by positivity
          have hqq : (0 : ℝ) ≤ ((ij.2 + k : ℕ) : ℝ) ^ (ij.2 + k) := by positivity
          calc (j.choose ij.1 : ℝ) * (K * ((k + σ : ℕ) : ℝ) ^ ij.1) * wN χ u (ij.2 + k)
              ≤ (j.choose ij.1 : ℝ) * (K * (s : ℝ) ^ ij.1) *
                  (B * L ^ (ij.2 + k) * ((ij.2 + k : ℕ) : ℝ) ^ (ij.2 + k)) := by
                gcongr
            _ = (j.choose ij.1 : ℝ) * K * B * (L ^ (ij.2 + k) *
                  ((s : ℝ) ^ ij.1 * ((ij.2 + k : ℕ) : ℝ) ^ (ij.2 + k))) := by ring
            _ ≤ (j.choose ij.1 : ℝ) * K * B * (L ^ s * (s : ℝ) ^ s) := by gcongr
            _ = _ := by ring
      _ = (∑ ij ∈ antidiagonal j, (j.choose ij.1 : ℝ)) * K * (B * L ^ s * (s : ℝ) ^ s) := by
          rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ 2 ^ σ * K * (B * L ^ s * (s : ℝ) ^ s) := by
          rw [sum_antidiagonal_choose_eq]
          have : (0 : ℝ) ≤ B * L ^ s * (s : ℝ) ^ s := by positivity
          gcongr
          · norm_num
  have hmain := hsD_le_of_sobolev hu hu_c hχ h01 hK0 hK hσL hCS hsob k hy
  have hss : (s : ℝ) ^ s ≤ e ^ s * (2 ^ s * k.factorial * σ.factorial) :=
    (pow_self_le_exp_mul_factorial s).trans (by gcongr; exact factorial_add_le k σ)
  calc ‖iteratedFDeriv ℝ k u y‖ ≤ hsD k u y := norm_iteratedFDeriv_le_hsD k u y
    _ ≤ CS * (2 ^ σ * K * (B * L ^ s * (s : ℝ) ^ s) + 2 ^ σ * K * (B * L ^ s * (s : ℝ) ^ s)) :=
        hmain.trans (mul_le_mul_of_nonneg_left (add_le_add (hterm 0 (Nat.zero_le _))
          (hterm σ le_rfl)) hCS)
    _ = CS * (2 * 2 ^ σ * K * B) * (L ^ s * (s : ℝ) ^ s) := by ring
    _ ≤ CS * (2 * 2 ^ σ * K * B) * (L ^ s * (e ^ s * (2 ^ s * k.factorial * σ.factorial))) := by
        have : 0 ≤ CS * (2 * 2 ^ σ * K * B) := by positivity
        gcongr
    _ = CS * (2 * 2 ^ σ * K * B) * (σ.factorial * (2 * e * L) ^ σ) * (2 * e * L) ^ k *
          k.factorial := by
        rw [hs]; ring

theorem exists_coef_bound {A : Finset (Fin n → ℕ)}
    {a : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ} {x₀ : EuclideanSpace ℝ (Fin n)}
    (ha : ∀ α ∈ A, AnalyticAt ℝ (a α) x₀) :
    ∃ ρ > 0, ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ α ∈ A, ∀ y ∈ Metric.ball x₀ ρ, ∀ k : ℕ,
      ‖iteratedFDeriv ℝ k (a α) y‖ ≤ C * M ^ k * k.factorial := by
  classical
  have h := fun α (hα : α ∈ A) ↦ exists_norm_iteratedFDeriv_le_of_analyticAt (ha α hα)
  choose! r hr C M hC hM hb using h
  have hev : ∀ᶠ y in nhds x₀, ∀ α ∈ A, y ∈ Metric.ball x₀ (r α) :=
    (Filter.eventually_all_finset A).2 fun α hα ↦ Metric.ball_mem_nhds x₀ (hr α hα)
  obtain ⟨ρ, hρ, hρb⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨ρ, hρ, ∑ α ∈ A, C α, ∑ α ∈ A, M α, Finset.sum_nonneg fun α hα ↦ hC α hα,
    Finset.sum_nonneg fun α hα ↦ hM α hα, fun α hα y hy k ↦ ?_⟩
  have h1 : C α ≤ ∑ β ∈ A, C β := Finset.single_le_sum (fun β hβ ↦ hC β hβ) hα
  have h2 : M α ≤ ∑ β ∈ A, M β := Finset.single_le_sum (fun β hβ ↦ hM β hβ) hα
  have hC0 := hC α hα
  have hM0 := hM α hα
  have hS0 : 0 ≤ ∑ β ∈ A, C β := le_trans hC0 h1
  calc ‖iteratedFDeriv ℝ k (a α) y‖ ≤ C α * M α ^ k * k.factorial :=
        hb α hα y (hρb y hy α hα) k
    _ ≤ (∑ β ∈ A, C β) * (∑ β ∈ A, M β) ^ k * k.factorial := by gcongr

theorem analyticAt_of_elliptic_of_pos (hn : 0 < n) {m : ℕ} (hm : 1 ≤ m)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    {A : Finset (Fin n → ℕ)} {a : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ}
    (hA : ∀ α ∈ A, mabs α ≤ m) (ha : ∀ α ∈ A, AnalyticOn ℝ (a α) Ω)
    (hell : ∀ x ∈ Ω, ∀ ξ : EuclideanSpace ℝ (Fin n), ξ ≠ 0 → prinSymbol A a m x ξ ≠ 0)
    {u : EuclideanSpace ℝ (Fin n) → ℂ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hDu : ∀ x ∈ Ω, diffOp A a u x = 0) {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω) :
    AnalyticAt ℝ u x₀ := by
  classical
  have haAt : ∀ α ∈ A, AnalyticAt ℝ (a α) x₀ := fun α hα ↦
    (hΩ.analyticOn_iff_analyticOnNhd.1 (ha α hα)) x₀ hx₀
  obtain ⟨ρ, hρ, Ca0, Ma0, hCa0, hMa0, hcb⟩ := exists_coef_bound haAt
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 hΩ x₀ hx₀
  set R₁ := min ε ρ with hR₁
  have hR₁0 : 0 < R₁ := lt_min hε hρ

  obtain ⟨θ, hθ, hθc, _, hθs, hθ1⟩ := exists_cutoff x₀ hR₁0
  have hθC : ContDiff ℝ ∞ (fun y ↦ ((θ y : ℂ))) := Complex.ofRealCLM.contDiff.comp hθ
  have hθc' : HasCompactSupport (fun y ↦ ((θ y : ℂ))) :=
    hθc.comp_left (g := fun t : ℝ ↦ (t : ℂ)) Complex.ofReal_zero
  have hθΩ : tsupport (fun y ↦ ((θ y : ℂ))) ⊆ Ω :=
    (tsupport_comp_subset (g := fun t : ℝ ↦ (t : ℂ)) Complex.ofReal_zero θ).trans
      (hθs.trans ((Metric.ball_subset_ball (min_le_left _ _)).trans hεΩ))
  have haC : ∀ α ∈ A, ContDiffOn ℝ ∞ (a α) Ω := fun α hα ↦
    (ha α hα).contDiffOn hΩ.uniqueDiffOn
  set ã : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ := fun α y ↦ ((θ y : ℂ)) * a α y with hã
  set ũ : EuclideanSpace ℝ (Fin n) → ℂ := fun y ↦ ((θ y : ℂ)) * u y with hũ
  have hãC : ∀ α ∈ A, ContDiff ℝ ∞ (ã α) := fun α hα ↦
    contDiff_mul_of_tsupport hΩ (haC α hα) hθC hθΩ
  have hũC : ContDiff ℝ ∞ ũ := contDiff_mul_of_tsupport hΩ hu hθC hθΩ
  have hũc : HasCompactSupport ũ := hθc'.mul_right

  have hbnd : ∀ α ∈ A, ∃ C, ∀ x, ‖ã α x‖ ≤ C := fun α hα ↦
    (hãC α hα).continuous.bounded_above_of_compact_support hθc'.mul_right
  choose! Cb hCb using hbnd
  set A₀ : ℝ := ∑ α ∈ A, |Cb α| with hA₀def
  have hA₀0 : 0 ≤ A₀ := Finset.sum_nonneg fun α _ ↦ abs_nonneg _
  have hA₀ : ∀ α ∈ A, ∀ x, ‖ã α x‖ ≤ A₀ := fun α hα x ↦
    (hCb α hα x).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun β ↦ |Cb β|) (fun β _ ↦ abs_nonneg _) hα))

  set R₂ := R₁ / 2 with hR₂
  have hR₂0 : 0 < R₂ := by positivity
  have hev : ∀ y ∈ Metric.ball x₀ R₂, (∀ α, ã α =ᶠ[nhds y] a α) ∧ ũ =ᶠ[nhds y] u := by
    intro y hy
    have hnb : Metric.ball x₀ R₂ ∈ nhds y := Metric.isOpen_ball.mem_nhds hy
    refine ⟨fun α ↦ ?_, ?_⟩
    · filter_upwards [hnb] with z hz
      simp [hã, hθ1 z hz]
    · filter_upwards [hnb] with z hz
      simp [hũ, hθ1 z hz]
  have hR₂Ω : Metric.ball x₀ R₂ ⊆ Ω :=
    (Metric.ball_subset_ball (by
      have : R₁ ≤ ε := min_le_left _ _
      linarith)).trans hεΩ
  have hR₂ρ : Metric.ball x₀ R₂ ⊆ Metric.ball x₀ ρ :=
    Metric.ball_subset_ball (by
      have : R₁ ≤ ρ := min_le_right _ _
      linarith)
  have hPu : ∀ y ∈ Metric.ball x₀ R₂, diffOp A ã ũ y = 0 := by
    intro y hy
    rw [← hDu y (hR₂Ω hy)]
    simp only [diffOp]
    refine Finset.sum_congr rfl fun α _ ↦ ?_
    rw [((hev y hy).1 α).eq_of_nhds, pderiv_eq_dT, pderiv_eq_dT,
      dT_congr_of_eventuallyEq (hev y hy).2]
  have hcoef : ∀ α ∈ A, ∀ y ∈ Metric.ball x₀ R₂, ∀ i,
      hsD i (ã α) y ≤ Ca0 * ((n : ℝ) * Ma0) ^ i * i.factorial := by
    intro α hα y hy i
    rw [hsD_congr_of_eventuallyEq ((hev y hy).1 α)]
    calc hsD i (a α) y ≤ (n : ℝ) ^ i * ‖iteratedFDeriv ℝ i (a α) y‖ :=
          hsD_le_norm_iteratedFDeriv i (a α) y
      _ ≤ (n : ℝ) ^ i * (Ca0 * Ma0 ^ i * i.factorial) := by
          gcongr; exact hcb α hα y (hR₂ρ hy) i
      _ = Ca0 * ((n : ℝ) * Ma0) ^ i * i.factorial := by ring

  have hx₀R₂ : x₀ ∈ Metric.ball x₀ R₂ := Metric.mem_ball_self hR₂0
  have hell0 : ∀ ξ : EuclideanSpace ℝ (Fin n), ξ ≠ 0 → prinSymbol A ã m x₀ ξ ≠ 0 := by
    intro ξ hξ
    have e : prinSymbol A ã m x₀ ξ = prinSymbol A a m x₀ ξ := by
      simp only [prinSymbol, hã, hθ1 x₀ hx₀R₂, Complex.ofReal_one, one_mul]
    rw [e]
    exact hell x₀ hx₀ ξ hξ
  obtain ⟨R₀, hR₀, C₀, hC₀, hE⟩ :=
    elliptic_estimate (Or.inl hn) hA (fun α hα ↦ (hãC α hα).continuous) hell0

  set R := min R₂ R₀ with hR
  have hR0 : 0 < R := lt_min hR₂0 hR₀
  obtain ⟨χ, hχ, hχc, h01, hχs, hχ1⟩ := exists_cutoff x₀ hR0
  have hUR₂ : Metric.ball x₀ R ⊆ Metric.ball x₀ R₂ := Metric.ball_subset_ball (min_le_left _ _)
  have hUR₀ : Metric.ball x₀ R ⊆ Metric.ball x₀ R₀ := Metric.ball_subset_ball (min_le_right _ _)
  obtain ⟨σ, CS, hCS, hsob⟩ := sobolev_pointwise (n := n)
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_norm_iteratedFDeriv_pow_le hχ hχc h01 (m + σ)
  set K : ℝ := max 1 (n : ℝ) ^ (m + σ) * K₁ with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hK : ∀ (s i : ℕ) (x : EuclideanSpace ℝ (Fin n)), i ≤ m + σ → i ≤ s →
      hsD i (fun y ↦ ((χ y : ℂ)) ^ s) x ≤ K * (s : ℝ) ^ i * χ x ^ (s - i) := by
    intro s i x hi his
    have hni : (n : ℝ) ^ i ≤ max 1 (n : ℝ) ^ (m + σ) :=
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (le_max_right _ _) i).trans
        (pow_le_pow_right₀ (le_max_left _ _) hi)
    have hb := hK₁ s i x hi his
    have hχ0 := (h01 x).1
    calc hsD i (fun y ↦ ((χ y : ℂ)) ^ s) x
        ≤ (n : ℝ) ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ ((χ y : ℂ)) ^ s) x‖ :=
          hsD_le_norm_iteratedFDeriv _ _ _
      _ ≤ max 1 (n : ℝ) ^ (m + σ) * (K₁ * (s : ℝ) ^ i * χ x ^ (s - i)) := by gcongr
      _ = K * (s : ℝ) ^ i * χ x ^ (s - i) := by rw [hKdef]; ring
  have hKm : ∀ (s i : ℕ) (x : EuclideanSpace ℝ (Fin n)), i ≤ m → i ≤ s →
      hsD i (fun y ↦ ((χ y : ℂ)) ^ s) x ≤ K * (s : ℝ) ^ i * χ x ^ (s - i) :=
    fun s i x hi his ↦ hK s i x (by omega) his
  have hE' : ∀ v : EuclideanSpace ℝ (Fin n) → ℂ, ContDiff ℝ ∞ v → HasCompactSupport v →
      tsupport v ⊆ Metric.ball x₀ R → l2n (hsD m v) ≤
        C₀ * (l2n (fun x ↦ ‖diffOp A ã v x‖) + ∑ j ∈ range m, l2n (hsD j v)) :=
    fun v h1 h2 h3 ↦ hE v h1 h2 (h3.trans hUR₀)
  obtain ⟨B, L, hB, hL, hN⟩ := weighted_derivative_bound hm hãC hA₀0 hA₀ hA hũC hũc
    Metric.isOpen_ball (fun y hy ↦ hPu y (hUR₂ hy)) hχ h01 hχs hCa0
    (by positivity : (0 : ℝ) ≤ (n : ℝ) * Ma0) (fun α hα y hy i ↦ hcoef α hα y (hUR₂ hy) i)
    hC₀ hE' hK0 hKm
  obtain ⟨C, M, hbound⟩ := exists_norm_iteratedFDeriv_le_of_wN hũC hũc hχ h01 hK0 hK
    (σ := σ) (by omega) hCS hsob hB hL hN
  have hhalf : Metric.ball x₀ (R / 2) ⊆ Metric.ball x₀ R₂ :=
    (Metric.ball_subset_ball (by linarith)).trans hUR₂
  refine analyticAt_of_norm_iteratedFDeriv_le (r := R / 2) (C := C) (M := M) (by positivity)
    (hu.mono (hhalf.trans hR₂Ω)) fun y hy k ↦ ?_
  rw [← (((hev y (hhalf hy)).2).iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]
  exact hbound k y (hχ1 y hy)

theorem analyticOn_of_elliptic {m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    {A : Finset (Fin n → ℕ)} {a : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ}
    (hA : ∀ α ∈ A, mabs α ≤ m) (ha : ∀ α ∈ A, AnalyticOn ℝ (a α) Ω)
    (hell : ∀ x ∈ Ω, ∀ ξ : EuclideanSpace ℝ (Fin n), ξ ≠ 0 → prinSymbol A a m x ξ ≠ 0)
    {u : EuclideanSpace ℝ (Fin n) → ℂ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hDu : ∀ x ∈ Ω, diffOp A a u x = 0) : AnalyticOn ℝ u Ω := by
  intro x₀ hx₀
  refine AnalyticAt.analyticWithinAt ?_
  rcases Nat.eq_zero_or_pos n with hn | hn
  ·
    subst hn
    have hpt : ∀ y : EuclideanSpace ℝ (Fin 0), y = x₀ := fun y ↦ by
      ext i; exact Fin.elim0 i
    exact (analyticAt_const (v := u x₀)).congr
      (Filter.Eventually.of_forall fun y ↦ by rw [hpt y])
  rcases Nat.eq_zero_or_pos m with hm | hm
  ·
    subst hm
    have hA0 : ∀ α ∈ A, ∀ i, α i = 0 := fun α hα i ↦ by
      have h := hA α hα
      have h0 : mabs α = 0 := Nat.le_zero.1 h
      exact (Finset.sum_eq_zero_iff.1 h0) i (Finset.mem_univ _)
    have hzero : ∀ x ∈ Ω, u x = 0 := by
      intro x hx
      set ξ₀ : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, hn⟩ 1
      have hξ₀ : ξ₀ ≠ 0 := by
        intro h
        have := congrArg (fun z : EuclideanSpace ℝ (Fin n) ↦ z ⟨0, hn⟩) h
        simp [ξ₀] at this
      have hs := hell x hx ξ₀ hξ₀
      have hmp : ∀ α ∈ A, mpow α ξ₀ = 1 := fun α hα ↦ by
        simp [mpow, hA0 α hα]
      have hfilt : A.filter (fun α ↦ mabs α = 0) = A :=
        Finset.filter_true_of_mem fun α hα ↦ Nat.le_zero.1 (hA α hα)
      have hsym : prinSymbol A a 0 x ξ₀ = ∑ α ∈ A, a α x := by
        simp only [prinSymbol, hfilt]
        exact Finset.sum_congr rfl fun α hα ↦ by rw [hmp α hα]; simp
      have hpd : ∀ α ∈ A, pderiv α u x = u x := by
        intro α hα
        have key : ∀ (j : ℕ), j = 0 → ∀ v : Fin j → EuclideanSpace ℝ (Fin n),
            iteratedFDeriv ℝ j u x v = u x := by
          rintro j rfl v
          simp
        exact key _ (Nat.le_zero.1 (hA α hα)) _
      have hD := hDu x hx
      simp only [diffOp] at hD
      rw [Finset.sum_congr rfl fun α hα ↦ by rw [hpd α hα], ← Finset.sum_mul] at hD
      rw [hsym] at hs
      exact (mul_eq_zero.1 hD).resolve_left hs
    refine (analyticAt_const (v := (0 : ℂ))).congr ?_
    filter_upwards [hΩ.mem_nhds hx₀] with y hy
    exact (hzero y hy).symm
  exact analyticAt_of_elliptic_of_pos hn hm hΩ hA ha hell hu hDu hx₀

end

end GroundTheory.Automorphic.Sobolev
