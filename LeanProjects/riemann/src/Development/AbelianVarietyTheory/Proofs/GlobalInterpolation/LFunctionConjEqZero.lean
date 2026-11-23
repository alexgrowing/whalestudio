import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivativeBound
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NegSumLogDerivNonneg
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivDirichletLFunctionLocalZeroSum
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NegReLogDerivPrincipalLFunctionLe

open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open scoped ComplexConjugate

namespace GlobalTheory.ZeroFreeComplex

private theorem conj_apply_lemma {d : ℕ} {χ : DirichletCharacter ℂ d} (h2 : χ ^ 2 = 1)
    (n : ℕ) : conj (χ n) = χ n := by
  by_cases hu : IsUnit (n : ZMod d)
  · have hsq : χ n * χ n = 1 := by
      have h := congrArg (fun ψ : DirichletCharacter ℂ d => ψ n) h2
      simp only [MulChar.pow_apply' χ two_ne_zero, MulChar.one_apply hu] at h
      simpa [pow_two] using h
    rcases mul_self_eq_one_iff.mp hsq with h | h <;> simp [h]
  · simp [MulChar.map_nonunit χ hu]

private theorem conj_LFunction_conj_of_sq_eq_one' {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}
    (h2 : χ ^ 2 = 1) {z : ℂ} (hz : 1 < z.re) :
    conj (LFunction χ (conj z)) = LFunction χ z := by
  have hz' : 1 < (conj z).re := by simpa using hz
  rw [LFunction_eq_LSeries χ hz, LFunction_eq_LSeries χ hz']
  unfold LSeries
  rw [Complex.conj_tsum]
  congr 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀, conj_apply_lemma h2]
    congr 1
    rw [Complex.cpow_conj _ _ (by rw [Complex.natCast_arg]; exact Real.pi_pos.ne), Complex.conj_conj,
      Complex.conj_natCast]

theorem LFunction_conj_eq_zero {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d} (h₁ : χ ≠ 1)
    (h2 : χ ^ 2 = 1) {s : ℂ} (hs : LFunction χ s = 0) : LFunction χ (conj s) = 0 := by
  have hd : Differentiable ℂ (LFunction χ) := differentiable_LFunction h₁
  have hg : Differentiable ℂ (conj ∘ LFunction χ ∘ conj) := by
    intro z
    have h := (hd (conj z)).conj_conj
    rwa [Complex.conj_conj] at h
  have heq : (conj ∘ LFunction χ ∘ conj) = LFunction χ := by
    refine AnalyticOnNhd.eq_of_eventuallyEq (analyticOnNhd_univ_iff_differentiable.mpr hg)
      (analyticOnNhd_univ_iff_differentiable.mpr hd) (z₀ := 2) ?_
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    exact conj_LFunction_conj_of_sq_eq_one' h2 hz
  have h := congrFun heq (conj s)
  simp only [Function.comp_apply, Complex.conj_conj, hs, _root_.map_zero] at h
  exact h.symm

theorem one_le_order {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (h : χ ≠ 1) {ρ : ℂ}
    (hρ : LFunction χ ρ = 0) : 1 ≤ analyticOrderNatAt (LFunction χ) ρ := by
  have hd : Differentiable ℂ (LFunction χ) := differentiable_LFunction h
  have ha : AnalyticOnNhd ℂ (LFunction χ) Set.univ := analyticOnNhd_univ_iff_differentiable.mpr hd
  have h2 : LFunction χ 2 ≠ 0 := LFunction_ne_zero_of_one_le_re χ (Or.inl h) (by norm_num)
  have hfin2 : analyticOrderAt (LFunction χ) 2 ≠ ⊤ := by
    rw [(ha 2 trivial).analyticOrderAt_eq_zero.mpr h2]
    exact ENat.zero_ne_top
  have hfin : analyticOrderAt (LFunction χ) ρ ≠ ⊤ :=
    ha.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ trivial trivial hfin2
  have hne : analyticOrderAt (LFunction χ) ρ ≠ 0 := (ha ρ trivial).analyticOrderAt_ne_zero.mpr hρ
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  apply hne
  rw [← Nat.cast_analyticOrderNatAt hfin, h0]
  rfl

theorem re_lt_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (h : χ ≠ 1) {ρ : ℂ}
    (hρ : LFunction χ ρ = 0) : ρ.re < 1 := by
  by_contra hle
  push Not at hle
  exact LFunction_ne_zero_of_one_le_re χ (Or.inl h) hle hρ

theorem neg_re_logDeriv_le : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ ≠ 1 → ∀ (σ t : ℝ), 1 < σ → σ ≤ 2 → ∀ S : Finset ℂ,
    (∀ w ∈ S, ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ LFunction χ w = 0) →
    -(deriv (LFunction χ) (σ + t * I) / LFunction χ (σ + t * I)).re
      ≤ C * Real.log (q * (|t| + 2)) - ∑ w ∈ S, (1 / ((σ : ℂ) + t * I - w)).re := by
  obtain ⟨C, hC, hloc⟩ := GlobalTheory.LLocal.logDeriv_LFunction_local
  refine ⟨C, hC, fun q _ χ hχ σ t hσ hσ2 S hS => ?_⟩
  have hdist : ‖((σ : ℂ) + t * I) - (3/2 + t * I)‖ ≤ 2/3 := by
    rw [show ((σ : ℂ) + t * I) - (3/2 + t * I) = ((σ - 3/2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hre_s : ((σ : ℂ) + t * I).re = σ := by simp
  have hLs : LFunction χ ((σ : ℂ) + t * I) ≠ 0 :=
    LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by rw [hre_s]; linarith)
  obtain ⟨hfin, hbound⟩ := hloc q χ hχ t ((σ : ℂ) + t * I) hdist hLs
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hbound
  set A := deriv (LFunction χ) ((σ : ℂ) + t * I) / LFunction χ ((σ : ℂ) + t * I) with hA
  set B := ∑ w ∈ hfin.toFinset,
    (analyticOrderNatAt (LFunction χ) w : ℂ) / ((σ : ℂ) + t * I - w) with hB
  have hAB : -A.re ≤ C * Real.log (q * (|t| + 2)) - B.re := by
    have h := (Complex.abs_re_le_norm (A - B)).trans hbound
    rw [Complex.sub_re, abs_le] at h
    linarith [h.1]
  have hpos : ∀ w, LFunction χ w = 0 → 0 ≤ (1 / ((σ : ℂ) + t * I - w)).re := by
    intro w hw
    have hw1 := re_lt_one hχ hw
    have hz : 0 < ((σ : ℂ) + t * I - w).re := by simp; linarith
    rw [one_div, Complex.inv_re]
    exact div_nonneg hz.le (Complex.normSq_nonneg _)
  have hBre : B.re = ∑ w ∈ hfin.toFinset,
      (analyticOrderNatAt (LFunction χ) w : ℝ) * (1 / ((σ : ℂ) + t * I - w)).re := by
    rw [hB, Complex.re_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [div_eq_mul_one_div, show ((analyticOrderNatAt (LFunction χ) w : ℕ) : ℂ) =
      ((analyticOrderNatAt (LFunction χ) w : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
  have hSsub : S ⊆ hfin.toFinset := by
    intro w hw
    rw [Set.Finite.mem_toFinset]
    exact hS w hw
  have hSle : ∑ w ∈ S, (1 / ((σ : ℂ) + t * I - w)).re ≤ B.re := by
    rw [hBre]
    calc ∑ w ∈ S, (1 / ((σ : ℂ) + t * I - w)).re
        ≤ ∑ w ∈ S, (analyticOrderNatAt (LFunction χ) w : ℝ) * (1 / ((σ : ℂ) + t * I - w)).re := by
          refine Finset.sum_le_sum fun w hw => ?_
          have hw0 := (hS w hw).2
          have h1 : (1 : ℝ) ≤ analyticOrderNatAt (LFunction χ) w := by
            exact_mod_cast one_le_order hχ hw0
          have h2 := hpos w hw0
          nlinarith
      _ ≤ ∑ w ∈ hfin.toFinset,
          (analyticOrderNatAt (LFunction χ) w : ℝ) * (1 / ((σ : ℂ) + t * I - w)).re := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hSsub fun w hw _ => ?_
          rw [Set.Finite.mem_toFinset] at hw
          exact mul_nonneg (Nat.cast_nonneg _) (hpos w hw.2)
  linarith

theorem re_one_div (a b : ℝ) : (1 / ((a : ℂ) + b * I)).re = a / (a ^ 2 + b ^ 2) := by
  rw [Complex.div_re, Complex.normSq_apply]
  simp
  ring

theorem half_lt_log (q : ℕ) [NeZero q] (t : ℝ) : 1 / 2 < Real.log (q * (|t| + 2)) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have h2 : (2 : ℝ) ≤ q * (|t| + 2) := by nlinarith [abs_nonneg t]
  have := Real.log_le_log (by norm_num) h2
  linarith [Real.log_two_gt_d9]

theorem log_zero_le (q : ℕ) [NeZero q] (t : ℝ) :
    Real.log (q * (|(0 : ℝ)| + 2)) ≤ Real.log (q * (|t| + 2)) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  apply Real.log_le_log
  · simp only [abs_zero, zero_add]; positivity
  · simp only [abs_zero, zero_add]
    nlinarith [abs_nonneg t]

theorem log_two_le (q : ℕ) [NeZero q] (t : ℝ) :
    Real.log (q * (|2 * t| + 2)) ≤ 2 * Real.log (q * (|t| + 2)) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have ht := abs_nonneg t
  rw [show (2 : ℝ) * Real.log (q * (|t| + 2)) = Real.log ((q * (|t| + 2)) ^ 2) by
    rw [Real.log_pow]; norm_num]
  apply Real.log_le_log (by positivity)
  rw [abs_mul, abs_two]
  have h1 : (q : ℝ) ≤ q * q := by nlinarith
  have h2 : 2 * |t| + 2 ≤ (|t| + 2) * (|t| + 2) := by nlinarith
  calc (q : ℝ) * (2 * |t| + 2) ≤ (q * q) * ((|t| + 2) * (|t| + 2)) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = (q * (|t| + 2)) ^ 2 := by ring

private theorem norm_ofReal_add_mul_I_le_of_sq_add_sq_le (a b r : ℝ) (hr : 0 ≤ r) (h : a ^ 2 + b ^ 2 ≤ r ^ 2) :
    ‖(a : ℂ) + b * I‖ ≤ r := by
  have h1 : ‖(a : ℂ) + b * I‖ ^ 2 = a ^ 2 + b ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  nlinarith [norm_nonneg ((a : ℂ) + b * I)]

theorem inv_le_log : ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ γ : ℝ), χ ≠ 1 → LFunction χ (((1 - δ : ℝ) : ℂ) + γ * I) = 0 → (χ ^ 2 ≠ 1 ∨ γ ≠ 0) →
    0 < δ → δ ≤ 1 / 21 → 1 / δ ≤ K * Real.log (q * (|γ| + 2)) := by
  obtain ⟨C1, hC1, h1⟩ := neg_re_logDeriv_le
  obtain ⟨C0, hC0, h0⟩ := GlobalTheory.PrincipalLogDeriv.neg_re_logDeriv_le
  refine ⟨300 * (C0 + C1), by positivity, fun q _ χ δ γ hχ hρ hcase hδ hδ21 => ?_⟩
  have hLpos : 0 < Real.log (q * (|γ| + 2)) := by linarith [half_lt_log q γ]
  have hL0 := log_zero_le q γ
  have hL2 := log_two_le q γ
  set L := Real.log (q * (|γ| + 2)) with hL_def
  have hC0L : 0 < C0 * L := mul_pos hC0 hLpos
  have hC1L : 0 < C1 * L := mul_pos hC1 hLpos
  have hσ1 : 1 < 1 + 8 * δ := by linarith
  have hσ2 : 1 + 8 * δ ≤ 2 := by linarith
  have hA : -(deriv (LFunction (1 : DirichletCharacter ℂ q)) ((1 + 8 * δ : ℝ) : ℂ) /
      LFunction (1 : DirichletCharacter ℂ q) ((1 + 8 * δ : ℝ) : ℂ)).re ≤ 1 / δ / 8 + C0 * L := by
    have h := h0 q (1 + 8 * δ) 0 hσ1 hσ2
    rw [show (((1 + 8 * δ : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) = ((1 + 8 * δ : ℝ) : ℂ) by simp] at h
    rw [show ((1 + 8 * δ : ℝ) : ℂ) - 1 = ((8 * δ : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I by push_cast; ring,
      re_one_div] at h
    have e : 8 * δ / ((8 * δ) ^ 2 + 0 ^ 2) = 1 / δ / 8 := by field_simp; ring
    rw [e] at h
    have hk : C0 * Real.log (q * (|(0 : ℝ)| + 2)) ≤ C0 * L := mul_le_mul_of_nonneg_left hL0 hC0.le
    simp only [abs_zero, zero_add] at h hk
    linarith
  have hρ3 : ‖(((1 - δ : ℝ) : ℂ) + γ * I) - (3/2 + γ * I)‖ ≤ 5/6 := by
    rw [show (((1 - δ : ℝ) : ℂ) + γ * I) - (3/2 + γ * I) = ((-(1/2) - δ : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  have hB : -(deriv (LFunction χ) (((1 + 8 * δ : ℝ) : ℂ) + γ * I) /
      LFunction χ (((1 + 8 * δ : ℝ) : ℂ) + γ * I)).re ≤ C1 * L - 1 / δ / 9 := by
    have h := h1 q χ hχ (1 + 8 * δ) γ hσ1 hσ2 {((1 - δ : ℝ) : ℂ) + γ * I} (by
      intro w hw
      rw [Finset.mem_singleton] at hw
      rw [hw]
      exact ⟨hρ3, hρ⟩)
    rw [Finset.sum_singleton, show ((1 + 8 * δ : ℝ) : ℂ) + γ * I - (((1 - δ : ℝ) : ℂ) + γ * I) =
      ((9 * δ : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I by push_cast; ring, re_one_div] at h
    have e : 9 * δ / ((9 * δ) ^ 2 + 0 ^ 2) = 1 / δ / 9 := by field_simp; ring
    rw [e] at h
    exact h
  have hxpos : 0 < 1 / δ := by positivity
  by_cases h2 : χ ^ 2 = 1
  · have hγ : γ ≠ 0 := hcase.resolve_left (not_not.mpr h2)
    by_cases hsmall : 2 * γ ^ 2 ≤ 81 * δ ^ 2
    · have hcρ : LFunction χ (conj (((1 - δ : ℝ) : ℂ) + γ * I)) = 0 := LFunction_conj_eq_zero hχ h2 hρ
      have hconj : conj (((1 - δ : ℝ) : ℂ) + γ * I) = ((1 - δ : ℝ) : ℂ) + ((-γ : ℝ) : ℂ) * I := by
        apply Complex.ext <;> simp
      rw [hconj] at hcρ
      have hne : ((1 - δ : ℝ) : ℂ) + γ * I ≠ ((1 - δ : ℝ) : ℂ) + ((-γ : ℝ) : ℂ) * I := by
        intro h
        have := congrArg Complex.im h
        simp at this
        exact hγ (by linarith)
      have hdisk : ∀ w ∈ ({((1 - δ : ℝ) : ℂ) + γ * I, ((1 - δ : ℝ) : ℂ) + ((-γ : ℝ) : ℂ) * I} :
          Finset ℂ), ‖w - (3/2 + ((0 : ℝ) : ℂ) * I)‖ ≤ 5/6 ∧ LFunction χ w = 0 := by
        intro w hw
        rcases Finset.mem_insert.mp hw with hw | hw
        · rw [hw]
          refine ⟨?_, hρ⟩
          rw [show (((1 - δ : ℝ) : ℂ) + γ * I) - (3/2 + ((0 : ℝ) : ℂ) * I) =
            ((-(1/2) - δ : ℝ) : ℂ) + (γ : ℂ) * I by push_cast; ring]
          exact norm_ofReal_add_mul_I_le_of_sq_add_sq_le _ _ _ (by norm_num) (by nlinarith)
        · rw [Finset.mem_singleton] at hw
          rw [hw]
          refine ⟨?_, hcρ⟩
          rw [show (((1 - δ : ℝ) : ℂ) + ((-γ : ℝ) : ℂ) * I) - (3/2 + ((0 : ℝ) : ℂ) * I) =
            ((-(1/2) - δ : ℝ) : ℂ) + ((-γ : ℝ) : ℂ) * I by push_cast; ring]
          exact norm_ofReal_add_mul_I_le_of_sq_add_sq_le _ _ _ (by norm_num) (by nlinarith)
      have h := h1 q χ hχ (1 + 8 * δ) 0 hσ1 hσ2 _ hdisk
      rw [Finset.sum_pair hne] at h
      rw [show ((1 + 8 * δ : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I - (((1 - δ : ℝ) : ℂ) + γ * I) =
          ((9 * δ : ℝ) : ℂ) + ((-γ : ℝ) : ℂ) * I by push_cast; ring,
        show ((1 + 8 * δ : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I - (((1 - δ : ℝ) : ℂ) + ((-γ : ℝ) : ℂ) * I) =
          ((9 * δ : ℝ) : ℂ) + ((γ : ℝ) : ℂ) * I by push_cast; ring,
        re_one_div, re_one_div,
        show (((1 + 8 * δ : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) = ((1 + 8 * δ : ℝ) : ℂ) by simp] at h
      simp only [abs_zero, zero_add] at h
      set T := 9 * δ / ((9 * δ) ^ 2 + γ ^ 2) with hT
      have hlow : 2 / 27 * (1 / δ) ≤ T := by
        rw [hT]
        rw [div_mul_eq_mul_div, mul_one_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      rw [neg_sq] at h
      have H := GlobalTheory.TwoRealCharacters.neg_sum_logDeriv_nonneg q χ χ (1 + 8 * δ) h2 h2 hσ1
      rw [show χ * χ = 1 by rw [← sq]; exact h2] at H
      have hk : C1 * Real.log (q * (|(0 : ℝ)| + 2)) ≤ C1 * L := mul_le_mul_of_nonneg_left hL0 hC1.le
      simp only [abs_zero, zero_add] at hk
      have hb : -(deriv (LFunction χ) ((1 + 8 * δ : ℝ) : ℂ) / LFunction χ ((1 + 8 * δ : ℝ) : ℂ)).re
          ≤ C1 * L - 4 / 27 * (1 / δ) := by linarith
      linarith
    · push Not at hsmall
      have hC : -(deriv (LFunction (1 : DirichletCharacter ℂ q)) (((1 + 8 * δ : ℝ) : ℂ) + 2 * γ * I) /
          LFunction (1 : DirichletCharacter ℂ q) (((1 + 8 * δ : ℝ) : ℂ) + 2 * γ * I)).re
          ≤ 4 / 81 * (1 / δ) + 2 * C0 * L := by
        have h := h0 q (1 + 8 * δ) (2 * γ) hσ1 hσ2
        rw [show ((1 + 8 * δ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * I - 1 =
          ((8 * δ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * I by push_cast; ring, re_one_div] at h
        have e : 8 * δ / ((8 * δ) ^ 2 + (2 * γ) ^ 2) ≤ 4 / 81 * (1 / δ) := by
          rw [div_mul_eq_mul_div, mul_one_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        push_cast at h ⊢
        linarith [mul_le_mul_of_nonneg_left hL2 hC0.le]
      have H := GlobalTheory.logDerivativeThreeFourOne.three_four_one q χ (1 + 8 * δ) γ hσ1
      rw [h2] at H
      push_cast at H hA hB hC
      linarith
  · have hC : -(deriv (LFunction (χ ^ 2)) (((1 + 8 * δ : ℝ) : ℂ) + 2 * γ * I) /
        LFunction (χ ^ 2) (((1 + 8 * δ : ℝ) : ℂ) + 2 * γ * I)).re ≤ 2 * C1 * L := by
      have h := h1 q (χ ^ 2) h2 (1 + 8 * δ) (2 * γ) hσ1 hσ2 ∅ (by simp)
      rw [Finset.sum_empty, sub_zero] at h
      push_cast at h ⊢
      linarith [mul_le_mul_of_nonneg_left hL2 hC1.le]
    have H := GlobalTheory.logDerivativeThreeFourOne.three_four_one q χ (1 + 8 * δ) γ hσ1
    push_cast at H hA hB hC
    linarith

theorem zero_free_region : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), χ ≠ 1 → LFunction χ s = 0 → (χ ^ 2 ≠ 1 ∨ s.im ≠ 0) → s.re < 1 - c / Real.log (q * (|s.im| + 2)) := by
  obtain ⟨K, hK, hKb⟩ := inv_le_log
  refine ⟨min (1 / (2 * K)) (1 / 42), by positivity, fun q _ χ s hχ hs hcase => ?_⟩
  have hL : 1 / 2 < Real.log (q * (|s.im| + 2)) := half_lt_log q s.im
  set L := Real.log (q * (|s.im| + 2)) with hL_def
  have hLpos : 0 < L := by linarith
  have hre := re_lt_one hχ hs
  have hδ : 0 < 1 - s.re := by linarith
  have hcL : min (1 / (2 * K)) (1 / 42) / L < 1 - s.re := by
    rw [div_lt_iff₀ hLpos]
    by_cases hsmall : 1 - s.re ≤ 1 / 21
    · have hs' : LFunction χ (((1 - (1 - s.re) : ℝ) : ℂ) + s.im * I) = 0 := by
        rw [show (((1 - (1 - s.re) : ℝ) : ℂ) + s.im * I) = s by
          apply Complex.ext <;> simp]
        exact hs
      have hb := hKb q χ (1 - s.re) s.im hχ hs' hcase hδ hsmall
      rw [div_le_iff₀ hδ] at hb
      have hm : min (1 / (2 * K)) (1 / 42) ≤ 1 / (2 * K) := min_le_left _ _
      have hk : 1 / (2 * K) < (1 - s.re) * L := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
    · push Not at hsmall
      have hm : min (1 / (2 * K)) (1 / 42) ≤ 1 / 42 := min_le_right _ _
      nlinarith
  linarith

end GlobalTheory.ZeroFreeComplex
