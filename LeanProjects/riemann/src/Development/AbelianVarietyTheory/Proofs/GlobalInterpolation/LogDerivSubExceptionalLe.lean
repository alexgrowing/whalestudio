import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionFamilyContinuationGrowthStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassFamilyLogDerivReGtOneStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionLogDerivLocalFormulaStatement

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk.LogDerivHalf

lemma one_le_ell (𝓕 : LFam) (t : ℝ) : 1 ≤ 𝓕.ell t := by
  linarith [𝓕.two_lt_ell t]

lemma ell_le (𝓕 : LFam) (t u : ℝ) (h : |u - t| ≤ 3 / 5) : 𝓕.ell u ≤ 4 / 3 * 𝓕.ell t := by
  have hB : (4 : ℝ) ≤ 𝓕.B := 𝓕.B_ge
  have h2 := 𝓕.two_lt_ell t
  have hu : |u| ≤ |t| + 3 / 5 := by
    have := abs_sub_abs_le_abs_sub u t
    linarith
  have ht0 := abs_nonneg t
  have hpos : 0 < 𝓕.B * (|u| + 2) := by positivity
  have hle : 𝓕.B * (|u| + 2) ≤ 𝓕.B * (|t| + 2) * (13 / 10) := by
    have : |u| + 2 ≤ (|t| + 2) * (13 / 10) := by linarith
    nlinarith
  have hlog : Real.log (𝓕.B * (|u| + 2)) ≤ Real.log (𝓕.B * (|t| + 2)) + Real.log (13 / 10) := by
    rw [← Real.log_mul (by positivity) (by norm_num)]
    exact Real.log_le_log hpos hle
  have h13 : Real.log (13 / 10 : ℝ) ≤ 3 / 10 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 13 / 10 by norm_num)
    linarith
  unfold LFam.ell at h2 ⊢
  linarith

lemma order_eq_one {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (h0 : f z = 0) (h1 : deriv f z ≠ 0) :
    analyticOrderNatAt f z = 1 := by
  simp [analyticOrderNatAt, hf.analyticOrderAt_eq_one_of_zero_deriv_ne_zero h0 h1]

lemma norm_lamChi_le (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (n : ℕ) : ‖𝓕.lamChi χ n‖ ≤ 2 * Λ n := by
  unfold LFam.lamChi
  calc ‖∑ g, χ g * (𝓕.lam g n : ℂ)‖ ≤ ∑ g, ‖χ g * (𝓕.lam g n : ℂ)‖ := norm_sum_le _ _
    _ = ∑ g, 𝓕.lam g n := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [norm_mul, AddChar.norm_apply, one_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (𝓕.lam_nonneg g n)]
    _ ≤ 2 * Λ n := 𝓕.lam_le n

lemma exists_bound_LSeries : ∃ K : ℝ, 0 ≤ K ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (s : ℂ), 7 / 4 ≤ s.re →
    ‖LSeries (𝓕.lamChi χ) s‖ ≤ K := by
  set s₀ : ℂ := ((7 / 4 : ℝ) : ℂ) with hs₀
  have hs₀re : s₀.re = 7 / 4 := by simp [hs₀]
  have hΛ : Summable fun n => ‖LSeries.term (fun n => (Λ n : ℂ)) s₀ n‖ :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (by rw [hs₀re]; norm_num)).norm
  refine ⟨2 * ∑' n, ‖LSeries.term (fun n => (Λ n : ℂ)) s₀ n‖,
    mul_nonneg (by norm_num) (tsum_nonneg fun _ => norm_nonneg _), ?_⟩
  intro 𝓕 χ s hs
  have P : ∀ n, ‖LSeries.term (𝓕.lamChi χ) s n‖ ≤ 2 * ‖LSeries.term (fun n => (Λ n : ℂ)) s₀ n‖ := by
    intro n
    calc ‖LSeries.term (𝓕.lamChi χ) s n‖ ≤ ‖LSeries.term (𝓕.lamChi χ) s₀ n‖ :=
          LSeries.norm_term_le_of_re_le_re _ (by rw [hs₀re]; exact hs) n
      _ ≤ ‖LSeries.term (fun n => 2 * (Λ n : ℂ)) s₀ n‖ := by
          refine LSeries.norm_term_le _ ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          simpa using norm_lamChi_le 𝓕 χ n
      _ = 2 * ‖LSeries.term (fun n => (Λ n : ℂ)) s₀ n‖ := by
          rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
          split_ifs
          · simp
          · rw [norm_mul, mul_div_assoc]
            norm_num
  have hS : Summable fun n => ‖LSeries.term (𝓕.lamChi χ) s n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) P (hΛ.mul_left 2)
  calc ‖LSeries (𝓕.lamChi χ) s‖ = ‖∑' n, LSeries.term (𝓕.lamChi χ) s n‖ := rfl
    _ ≤ ∑' n, ‖LSeries.term (𝓕.lamChi χ) s n‖ := norm_tsum_le_tsum_norm hS
    _ ≤ ∑' n, 2 * ‖LSeries.term (fun n => (Λ n : ℂ)) s₀ n‖ := Summable.tsum_le_tsum P hS (hΛ.mul_left 2)
    _ = 2 * ∑' n, ‖LSeries.term (fun n => (Λ n : ℂ)) s₀ n‖ := tsum_mul_left

lemma norm_one_div_le {z : ℂ} {r : ℝ} (hr : 0 < r) (h : r ≤ ‖z‖) : ‖1 / z‖ ≤ 1 / r := by
  rw [norm_div, norm_one]
  exact one_div_le_one_div_of_le hr h

lemma sum_le_of_card_le_one {ι : Type*} {Z : Finset ι} (hZ : Z.card ≤ 1) {f : ι → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ i ∈ Z, ‖f i‖ ≤ M) : ‖∑ i ∈ Z, f i‖ ≤ M := by
  rcases Z.eq_empty_or_nonempty with hE | ⟨i, hi⟩
  · simpa [hE] using hM
  · have hZi : Z = {i} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hi, fun x hx => Finset.card_le_one.mp hZ x hx i hi⟩
    rw [hZi, Finset.sum_singleton]
    exact h i hi

theorem logDeriv_sub_exceptional_le : ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ 1 / 20 → ∃ C : ℝ, 0 < C ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (Z : Finset ℝ), 𝓕.ExcZ χ c₀ Z → ∀ s : ℂ, 1 - c₀ / 2 / 𝓕.ell s.im ≤ s.re → s.re ≤ 3 → (∀ β ∈ Z, s ≠ (β : ℂ)) → ‖deriv (𝓕.F χ) s / 𝓕.F χ s - ∑ β ∈ Z, 1 / (s - (β : ℂ))‖ ≤ C * 𝓕.ell s.im ^ 2 := by
  intro c₀ hc₀ hc₀'
  obtain ⟨C₁, hC₁, hW⟩ := GlobalTheory.T.rayClassLFunction_logDeriv_local_formula
  obtain ⟨K, hK, hKb⟩ := exists_bound_LSeries
  refine ⟨C₁ + 4 * C₁ / c₀ + 10 + K + 3, by positivity, ?_⟩
  intro 𝓕 χ Z hZ s hs1 hs3 hsZ
  have hℓ := 𝓕.two_lt_ell s.im
  have hℓsq : 𝓕.ell s.im ≤ 𝓕.ell s.im ^ 2 := by nlinarith
  have hℓ1 : 1 ≤ 𝓕.ell s.im ^ 2 := by nlinarith
  have hfinal : ∀ x : ℝ, x ≤ 10 → C₁ * 𝓕.ell s.im + C₁ * 𝓕.ell s.im * (4 * 𝓕.ell s.im / c₀) + x ≤
      (C₁ + 4 * C₁ / c₀ + 10 + K + 3) * 𝓕.ell s.im ^ 2 := by
    intro x hx
    have e : C₁ * 𝓕.ell s.im * (4 * 𝓕.ell s.im / c₀) = 4 * C₁ / c₀ * 𝓕.ell s.im ^ 2 := by ring
    have a1 : C₁ * 𝓕.ell s.im ≤ C₁ * 𝓕.ell s.im ^ 2 := mul_le_mul_of_nonneg_left hℓsq hC₁.le
    have a3 : 0 ≤ (K + 3) * 𝓕.ell s.im ^ 2 := by positivity
    nlinarith
  have hreg : 1 - c₀ / 𝓕.ell s.im ≤ s.re := by
    have : c₀ / 2 / 𝓕.ell s.im ≤ c₀ / 𝓕.ell s.im :=
      div_le_div_of_nonneg_right (by linarith) (by linarith)
    linarith
  have hFs : 𝓕.F χ s ≠ 0 := by
    intro h0
    obtain ⟨β, hβ, hsβ⟩ := hZ.2.2 s hreg h0
    exact hsZ β hβ hsβ
  have hsre : 3 / 4 ≤ s.re := by
    have : c₀ / 2 / 𝓕.ell s.im ≤ 1 / 4 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  by_cases hs74 : 7 / 4 ≤ s.re
  · obtain ⟨-, -, -, hL⟩ := GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one 𝓕 χ s (by linarith)
    have hdl : deriv (𝓕.F χ) s / 𝓕.F χ s =
        (if χ = 1 then 1 / (s - 1) else 0) - LSeries (𝓕.lamChi χ) s := by
      rw [← hL]
      ring
    have hpole : ‖(if χ = 1 then 1 / (s - 1) else 0 : ℂ)‖ ≤ 4 / 3 := by
      split_ifs
      · have h := norm_one_div_le (z := s - 1) (r := 3 / 4) (by norm_num)
          (by have := Complex.re_le_norm (s - 1); rw [Complex.sub_re, Complex.one_re] at this; linarith)
        linarith
      · norm_num
    have hexc : ‖∑ β ∈ Z, 1 / (s - (β : ℂ))‖ ≤ 4 / 3 := by
      refine sum_le_of_card_le_one hZ.1 (by norm_num) fun β hβ => ?_
      have hβ1 := (hZ.2.1 β hβ).2.1
      have h := norm_one_div_le (z := s - (β : ℂ)) (r := 3 / 4) (by norm_num)
        (by have := Complex.re_le_norm (s - (β : ℂ)); rw [Complex.sub_re, Complex.ofReal_re] at this; linarith)
      linarith
    have hLb := hKb 𝓕 χ s hs74
    rw [hdl]
    calc ‖(if χ = 1 then 1 / (s - 1) else 0) - LSeries (𝓕.lamChi χ) s - ∑ β ∈ Z, 1 / (s - (β : ℂ))‖
        ≤ ‖(if χ = 1 then 1 / (s - 1) else 0 : ℂ)‖ + ‖LSeries (𝓕.lamChi χ) s‖ + ‖∑ β ∈ Z, 1 / (s - (β : ℂ))‖ :=
          (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
      _ ≤ 4 / 3 + K + 4 / 3 := by linarith
      _ ≤ (C₁ + 4 * C₁ / c₀ + 10 + K + 3) * 𝓕.ell s.im ^ 2 := by
          have hA : 0 ≤ C₁ + 4 * C₁ / c₀ + 10 := by positivity
          nlinarith
  · push Not at hs74
    have hdisk : ‖s - (5 / 4 + s.im * I)‖ ≤ 1 / 2 := by
      have e : s - (5 / 4 + s.im * I) = ((s.re - 5 / 4 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    obtain ⟨hfin, hsum, hbd⟩ := hW 𝓕 χ s.im
    have h1 := hbd s hdisk hFs
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hsum h1
    have hterm : ∀ w ∈ hfin.toFinset, (¬ ∃ β ∈ Z, w = (β : ℂ)) →
        ‖(analyticOrderNatAt (𝓕.F χ) w : ℂ) / (s - w)‖ ≤
          (analyticOrderNatAt (𝓕.F χ) w : ℝ) * (4 * 𝓕.ell s.im / c₀) := by
      intro w hwT hnz
      have hw := hfin.mem_toFinset.mp hwT
      have hnotreg : w.re < 1 - c₀ / 𝓕.ell w.im := by
        by_contra h
        push Not at h
        exact hnz (hZ.2.2 w h hw.2)
      have him : |w.im - s.im| ≤ 3 / 5 := by
        have h := Complex.abs_im_le_norm (w - (5 / 4 + s.im * I))
        have e : (w - (5 / 4 + s.im * I)).im = w.im - s.im := by simp
        rw [e] at h
        exact h.trans hw.1
      have hℓw : 𝓕.ell w.im ≤ 4 / 3 * 𝓕.ell s.im := ell_le 𝓕 s.im w.im him
      have hℓw2 := 𝓕.two_lt_ell w.im
      have hgap : c₀ / (4 * 𝓕.ell s.im) ≤ (s - w).re := by
        rw [Complex.sub_re]
        have h3 : 3 * c₀ / (4 * 𝓕.ell s.im) ≤ c₀ / 𝓕.ell w.im := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_left hℓw hc₀.le]
        have e2 : c₀ / 2 / 𝓕.ell s.im = 2 * c₀ / (4 * 𝓕.ell s.im) := by
          field_simp
          ring
        have e3 : 3 * c₀ / (4 * 𝓕.ell s.im) - 2 * c₀ / (4 * 𝓕.ell s.im) = c₀ / (4 * 𝓕.ell s.im) := by
          ring
        linarith
      have h1d := norm_one_div_le (by positivity) (hgap.trans (Complex.re_le_norm _))
      rw [one_div_div] at h1d
      rw [show (analyticOrderNatAt (𝓕.F χ) w : ℂ) / (s - w) =
          (analyticOrderNatAt (𝓕.F χ) w : ℂ) * (1 / (s - w)) by ring, norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left h1d (Nat.cast_nonneg _)
    have key : ∀ S ⊆ hfin.toFinset, (∀ w ∈ S, ¬ ∃ β ∈ Z, w = (β : ℂ)) →
        ‖∑ w ∈ S, (analyticOrderNatAt (𝓕.F χ) w : ℂ) / (s - w)‖ ≤
          C₁ * 𝓕.ell s.im * (4 * 𝓕.ell s.im / c₀) := by
      intro S hS hSZ
      have hq : 0 ≤ 4 * 𝓕.ell s.im / c₀ := by positivity
      calc ‖∑ w ∈ S, (analyticOrderNatAt (𝓕.F χ) w : ℂ) / (s - w)‖
          ≤ ∑ w ∈ S, ‖(analyticOrderNatAt (𝓕.F χ) w : ℂ) / (s - w)‖ := norm_sum_le _ _
        _ ≤ ∑ w ∈ S, (analyticOrderNatAt (𝓕.F χ) w : ℝ) * (4 * 𝓕.ell s.im / c₀) :=
            Finset.sum_le_sum fun w hw => hterm w (hS hw) (hSZ w hw)
        _ = (∑ w ∈ S, (analyticOrderNatAt (𝓕.F χ) w : ℝ)) * (4 * 𝓕.ell s.im / c₀) :=
            (Finset.sum_mul _ _ _).symm
        _ ≤ (∑ w ∈ hfin.toFinset, (analyticOrderNatAt (𝓕.F χ) w : ℝ)) * (4 * 𝓕.ell s.im / c₀) :=
            mul_le_mul_of_nonneg_right
              (Finset.sum_le_sum_of_subset_of_nonneg hS fun _ _ _ => Nat.cast_nonneg _) hq
        _ ≤ C₁ * 𝓕.ell s.im * (4 * 𝓕.ell s.im / c₀) := mul_le_mul_of_nonneg_right hsum hq
    rcases Z.eq_empty_or_nonempty with hE | ⟨β, hβZ⟩
    · rw [hE, Finset.sum_empty, sub_zero]
      have hk := key hfin.toFinset subset_rfl (by rintro w - ⟨β, hβ, -⟩; simp [hE] at hβ)
      calc ‖deriv (𝓕.F χ) s / 𝓕.F χ s‖
          = ‖(deriv (𝓕.F χ) s / 𝓕.F χ s - ∑ w ∈ hfin.toFinset, (analyticOrderNatAt (𝓕.F χ) w : ℂ) / (s - w)) +
              ∑ w ∈ hfin.toFinset, (analyticOrderNatAt (𝓕.F χ) w : ℂ) / (s - w)‖ := by rw [sub_add_cancel]
        _ ≤ C₁ * 𝓕.ell s.im + C₁ * 𝓕.ell s.im * (4 * 𝓕.ell s.im / c₀) := (norm_add_le _ _).trans (add_le_add h1 hk)
        _ = C₁ * 𝓕.ell s.im + C₁ * 𝓕.ell s.im * (4 * 𝓕.ell s.im / c₀) + 0 := by ring
        _ ≤ _ := hfinal 0 (by norm_num)
    · have hZs : Z = {β} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hβZ, fun x hx => Finset.card_le_one.mp hZ.1 x hx β hβZ⟩
      have hβ := hZ.2.1 β hβZ
      have notZ : ∀ w : ℂ, w ≠ (β : ℂ) → ¬ ∃ β' ∈ Z, w = (β' : ℂ) := by
        rintro w hw ⟨β', hβ', rfl⟩
        rw [hZs, Finset.mem_singleton] at hβ'
        exact hw (by rw [hβ'])
      rw [hZs, Finset.sum_singleton]
      by_cases hβT : (β : ℂ) ∈ hfin.toFinset
      · have hhalf : 1 / 2 < (β : ℂ).re :=
          𝓕.half_lt_re_of_region (c := c₀) (by linarith) (s := (β : ℂ)) (by simpa using hβ.1)
        have hAn : AnalyticAt ℂ (𝓕.F χ) (β : ℂ) := (GlobalTheory.T.rayClassLFunctionFamily_continuation_growth 𝓕 χ).1 _ hhalf
        have hord : analyticOrderNatAt (𝓕.F χ) (β : ℂ) = 1 := order_eq_one hAn hβ.2.2.1 hβ.2.2.2
        have hk := key (hfin.toFinset.erase (β : ℂ)) (Finset.erase_subset _ _)
          fun w hw => notZ w (Finset.ne_of_mem_erase hw)
        have e : deriv (𝓕.F χ) s / 𝓕.F χ s - 1 / (s - (β : ℂ)) =
            (deriv (𝓕.F χ) s / 𝓕.F χ s - ∑ w ∈ hfin.toFinset, (analyticOrderNatAt (𝓕.F χ) w : ℂ) / (s - w)) +
              ∑ w ∈ hfin.toFinset.erase (β : ℂ), (analyticOrderNatAt (𝓕.F χ) w : ℂ) / (s - w) := by
          rw [← Finset.add_sum_erase _ _ hβT, hord, Nat.cast_one]
          ring
        rw [e]
        calc _ ≤ C₁ * 𝓕.ell s.im + C₁ * 𝓕.ell s.im * (4 * 𝓕.ell s.im / c₀) := (norm_add_le _ _).trans (add_le_add h1 hk)
          _ = C₁ * 𝓕.ell s.im + C₁ * 𝓕.ell s.im * (4 * 𝓕.ell s.im / c₀) + 0 := by ring
          _ ≤ _ := hfinal 0 (by norm_num)
      · have hk := key hfin.toFinset subset_rfl fun w hw => notZ w fun h => hβT (h ▸ hw)
        have hβW : ¬ (‖(β : ℂ) - (5 / 4 + s.im * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ β = 0) := fun h =>
          hβT (hfin.mem_toFinset.mpr h)
        have hfar : 3 / 5 < ‖(β : ℂ) - (5 / 4 + s.im * I)‖ := by
          by_contra h
          push Not at h
          exact hβW ⟨h, hβ.2.2.1⟩
        have hsβ : 1 / 10 ≤ ‖s - (β : ℂ)‖ := by
          have := norm_sub_le_norm_sub_add_norm_sub (β : ℂ) s (5 / 4 + s.im * I)
          rw [norm_sub_rev (β : ℂ) s] at this
          linarith
        have h10 : ‖1 / (s - (β : ℂ))‖ ≤ 10 := by
          have := norm_one_div_le (by norm_num) hsβ
          norm_num at this ⊢
          linarith
        calc ‖deriv (𝓕.F χ) s / 𝓕.F χ s - 1 / (s - (β : ℂ))‖
            = ‖(deriv (𝓕.F χ) s / 𝓕.F χ s - ∑ w ∈ hfin.toFinset, (analyticOrderNatAt (𝓕.F χ) w : ℂ) / (s - w)) +
                ∑ w ∈ hfin.toFinset, (analyticOrderNatAt (𝓕.F χ) w : ℂ) / (s - w) - 1 / (s - (β : ℂ))‖ := by
              rw [sub_add_cancel]
          _ ≤ ‖deriv (𝓕.F χ) s / 𝓕.F χ s - ∑ w ∈ hfin.toFinset, (analyticOrderNatAt (𝓕.F χ) w : ℂ) / (s - w)‖ +
                ‖∑ w ∈ hfin.toFinset, (analyticOrderNatAt (𝓕.F χ) w : ℂ) / (s - w)‖ + ‖1 / (s - (β : ℂ))‖ :=
              (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
          _ ≤ C₁ * 𝓕.ell s.im + C₁ * 𝓕.ell s.im * (4 * 𝓕.ell s.im / c₀) + 10 := by linarith
          _ ≤ _ := hfinal 10 le_rfl

end GlobalTheory.Hk.LogDerivHalf
