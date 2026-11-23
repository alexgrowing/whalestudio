import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionFamilyContinuationGrowthStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassFamilyLogDerivReGtOneStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionLogDerivLocalFormulaStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionFamilyLogDerivPositivityStatement

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk.ZeroFree

theorem re_one_div (a b : ℝ) : (1 / ((a : ℂ) + b * I)).re = a / (a ^ 2 + b ^ 2) := by
  rw [one_div, inv_re, normSq_add_mul_I]
  simp

theorem re_le_one {𝓕 : LFam} {χ : AddChar 𝓕.G ℂ} {w : ℂ} (hw : 𝓕.F χ w = 0) : w.re ≤ 1 := by
  by_contra h
  push_neg at h
  exact (GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one 𝓕 χ w h).2.2.1 hw

theorem one_le_order {𝓕 : LFam} {χ : AddChar 𝓕.G ℂ} {ρ : ℂ} (h : 1 / 2 < ρ.re)
    (hρ : 𝓕.F χ ρ = 0) : 1 ≤ analyticOrderNatAt (𝓕.F χ) ρ := by
  have hU := (GlobalTheory.T.rayClassLFunctionFamily_continuation_growth 𝓕 χ).1
  have hA : AnalyticAt ℂ (𝓕.F χ) ρ := hU ρ h
  have htop : analyticOrderAt (𝓕.F χ) ρ ≠ ⊤ := by
    intro ht
    rw [analyticOrderAt_eq_top] at ht
    have hc : Convex ℝ {s : ℂ | 1 / 2 < s.re} := convex_halfSpace_re_gt _
    have hE := hU.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc.isPreconnected h ht
    have h2 : (1 : ℝ) < (2 : ℂ).re := by norm_num
    exact (GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one 𝓕 χ 2 h2).2.2.1 (hE (show (1 : ℝ) / 2 < (2 : ℂ).re by norm_num))
  have hz : analyticOrderAt (𝓕.F χ) ρ ≠ 0 := hA.analyticOrderAt_ne_zero.mpr hρ
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  apply hz
  rw [← Nat.cast_analyticOrderNatAt htop, h0]
  simp

theorem re_LSeries_le : ∃ C : ℝ, 0 < C ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (a t P : ℝ),
    0 < a → a ≤ 1 / 2 → 0 ≤ P → (χ = 1 → a / (a ^ 2 + t ^ 2) ≤ P) → ∀ S : Finset ℂ,
    (∀ w ∈ S, ‖w - (5 / 4 + t * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0) →
    (LSeries (𝓕.lamChi χ) (((1 + a : ℝ) : ℂ) + t * I)).re
      ≤ P + C * 𝓕.ell t - ∑ w ∈ S, (1 / (((1 + a : ℝ) : ℂ) + t * I - w)).re := by
  obtain ⟨C, hC, hCb⟩ := GlobalTheory.T.rayClassLFunction_logDeriv_local_formula
  refine ⟨C, hC, ?_⟩
  intro 𝓕 χ a t P ha ha2 hP hχ S hS
  obtain ⟨hfin, -, hD⟩ := hCb 𝓕 χ t
  set s : ℂ := ((1 + a : ℝ) : ℂ) + t * I with hs
  have hsre : s.re = 1 + a := by simp [hs]
  have hsre1 : 1 < s.re := by rw [hsre]; linarith
  obtain ⟨-, -, hFne, hL⟩ := GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one 𝓕 χ s hsre1
  have hsd : ‖s - (5 / 4 + t * I)‖ ≤ 1 / 2 := by
    have e : s - (5 / 4 + t * I) = ((a - 1 / 4 : ℝ) : ℂ) := by rw [hs]; push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hE := hD s hsd hFne
  have hfpos : ∀ w, 𝓕.F χ w = 0 → 0 ≤ (1 / (s - w)).re := by
    intro w hw
    rw [one_div, inv_re]
    apply div_nonneg _ (normSq_nonneg _)
    rw [sub_re, hsre]
    linarith [re_le_one hw]
  have hsum : (∑ᶠ w ∈ {w : ℂ | ‖w - (5 / 4 + t * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0},
      (analyticOrderNatAt (𝓕.F χ) w : ℂ) / (s - w)).re
      = ∑ w ∈ hfin.toFinset, (analyticOrderNatAt (𝓕.F χ) w : ℝ) * (1 / (s - w)).re := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, re_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [div_eq_mul_one_div, ← ofReal_natCast, re_ofReal_mul]
  have hSZ : ∑ w ∈ S, (1 / (s - w)).re
      ≤ ∑ w ∈ hfin.toFinset, (analyticOrderNatAt (𝓕.F χ) w : ℝ) * (1 / (s - w)).re := by
    calc ∑ w ∈ S, (1 / (s - w)).re
        ≤ ∑ w ∈ S, (analyticOrderNatAt (𝓕.F χ) w : ℝ) * (1 / (s - w)).re := by
          apply Finset.sum_le_sum
          intro w hw
          obtain ⟨hw1, hw2⟩ := hS w hw
          have hre : 1 / 2 < w.re := by
            have h1 := (abs_le.mp ((abs_re_le_norm _).trans hw1)).1
            simp only [sub_re, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im] at h1
            norm_num at h1
            linarith
          have hm : (1 : ℝ) ≤ analyticOrderNatAt (𝓕.F χ) w := by
            exact_mod_cast one_le_order hre hw2
          nlinarith [hfpos w hw2]
      _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro w hw
            rw [Set.Finite.mem_toFinset]
            exact hS w hw
          · intro w hw _
            exact mul_nonneg (Nat.cast_nonneg _) (hfpos w ((Set.Finite.mem_toFinset hfin).mp hw).2)
  have hpole : (if χ = 1 then 1 / (s - 1) else 0 : ℂ).re ≤ P := by
    split_ifs with h1
    · have e : s - 1 = (a : ℂ) + t * I := by rw [hs]; push_cast; ring
      rw [e, re_one_div]
      exact hχ h1
    · simpa using hP
  rw [← hL, add_re, neg_re]
  have hre := (abs_le.mp ((abs_re_le_norm _).trans hE)).1
  rw [sub_re, hsum] at hre
  linarith

theorem one_le_ell (𝓕 : LFam) (t : ℝ) : 1 ≤ 𝓕.ell t := by
  have := 𝓕.two_lt_ell t
  linarith

theorem ell_zero_le (𝓕 : LFam) (t : ℝ) : 𝓕.ell 0 ≤ 𝓕.ell t := by
  unfold LFam.ell
  have hB : (0 : ℝ) < 𝓕.B := by linarith [𝓕.B_ge]
  rw [abs_zero]
  apply Real.log_le_log
  · positivity
  · apply mul_le_mul_of_nonneg_left _ hB.le
    linarith [abs_nonneg t]

theorem ell_two_le (𝓕 : LFam) (t : ℝ) : 𝓕.ell (2 * t) ≤ 2 * 𝓕.ell t := by
  unfold LFam.ell
  have hB : (4 : ℝ) ≤ 𝓕.B := 𝓕.B_ge
  have hu := abs_nonneg t
  have e : 2 * Real.log (𝓕.B * (|t| + 2)) = Real.log ((𝓕.B * (|t| + 2)) ^ 2) := by
    rw [Real.log_pow]
    norm_num
  rw [e, abs_mul, abs_two]
  apply Real.log_le_log
  · positivity
  · have h1 : 2 * |t| + 2 ≤ 4 * (|t| + 2) ^ 2 := by nlinarith
    have h2 : 4 * (|t| + 2) ^ 2 ≤ 𝓕.B * (|t| + 2) ^ 2 := by nlinarith [sq_nonneg (|t| + 2)]
    calc 𝓕.B * (2 * |t| + 2) ≤ 𝓕.B * (𝓕.B * (|t| + 2) ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ = (𝓕.B * (|t| + 2)) ^ 2 := by ring

theorem pole_le {ε y : ℝ} (hε : 0 < ε) (hy : (30 * ε) ^ 2 ≤ y ^ 2) :
    6 * ε / ((6 * ε) ^ 2 + y ^ 2) ≤ 1 / 156 * (1 / ε) := by
  have hD : 0 < (6 * ε) ^ 2 + y ^ 2 := by positivity
  have e : 1 / 156 * (1 / ε) = 1 / (156 * ε) := by ring
  rw [e, div_le_div_iff₀ hD (by positivity)]
  nlinarith

private lemma norm_ofReal_add_mul_I_le_abs_add_abs (x y : ℝ) : ‖(x : ℂ) + y * I‖ ≤ |x| + |y| := by
  simpa using norm_le_abs_re_add_abs_im ((x : ℂ) + y * I)

theorem inv_le_ell : ∃ K : ℝ, 0 < K ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (ε δ γ : ℝ),
    𝓕.F χ (((1 - δ : ℝ) : ℂ) + γ * I) = 0 → (χ * χ ≠ 1 ∨ γ ≠ 0) →
    0 < ε → ε ≤ 1 / 400 → 0 ≤ δ → δ ≤ ε → 1 / ε ≤ K * 𝓕.ell γ := by
  obtain ⟨C, hC, hR⟩ := re_LSeries_le
  refine ⟨300 * C, by positivity, ?_⟩
  intro 𝓕 χ ε δ γ hz hχ hε hε1 hδ hδε
  set ρ : ℂ := ((1 - δ : ℝ) : ℂ) + γ * I with hρ
  have hℓ0 := ell_zero_le 𝓕 γ
  have hℓ2 := ell_two_le 𝓕 γ
  have hℓ1 := one_le_ell 𝓕 γ
  have hCℓ0 : C * 𝓕.ell 0 ≤ C * 𝓕.ell γ := mul_le_mul_of_nonneg_left hℓ0 hC.le
  have hCℓ2 : C * 𝓕.ell (2 * γ) ≤ 2 * (C * 𝓕.ell γ) := by nlinarith
  have hCℓ : 0 ≤ C * 𝓕.ell γ := mul_nonneg hC.le (by linarith)
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = 1 / ε := ⟨_, rfl⟩
  have hv0 : 0 < v := by rw [hv]; positivity
  rw [← hv]
  by_cases hB : χ * χ = 1 ∧ γ ^ 2 < (30 * ε) ^ 2
  · obtain ⟨hχ2, hγ⟩ := hB
    have hγ0 : γ ≠ 0 := hχ.resolve_left (not_not.mpr hχ2)
    have ha0 : 0 < 60 * ε := by positivity
    have ha2 : 60 * ε ≤ 1 / 2 := by linarith
    set ρ' : ℂ := ((1 - δ : ℝ) : ℂ) + ((-γ : ℝ) : ℂ) * I with hρ'
    have hz' : 𝓕.F χ ρ' = 0 := by
      have hc := (GlobalTheory.T.rayClassLFunctionFamily_continuation_growth 𝓕 χ).2.2.2 hχ2 ρ
      have e : (starRingEnd ℂ) ρ = ρ' := by
        rw [hρ, hρ']
        apply Complex.ext <;> simp
      rw [← e, hc, hz]
      simp
    have hne : ρ ≠ ρ' := by
      intro h
      have := congrArg Complex.im h
      simp [hρ, hρ'] at this
      exact hγ0 (by linarith)
    have hγa : |γ| < 30 * ε := abs_lt_of_sq_lt_sq hγ (by linarith)
    have hnorm : ∀ g : ℝ, |g| < 30 * ε →
        ‖(((1 - δ : ℝ) : ℂ) + g * I) - (5 / 4 + ((0 : ℝ) : ℂ) * I)‖ ≤ 3 / 5 := by
      intro g hg
      have e : (((1 - δ : ℝ) : ℂ) + g * I) - (5 / 4 + ((0 : ℝ) : ℂ) * I)
          = ((-(1 / 4 + δ) : ℝ) : ℂ) + g * I := by push_cast; ring
      rw [e]
      refine (norm_ofReal_add_mul_I_le_abs_add_abs _ _).trans ?_
      rw [abs_neg, abs_of_nonneg (by linarith)]
      linarith
    have hnear : ∀ w ∈ ({ρ, ρ'} : Finset ℂ),
        ‖w - (5 / 4 + ((0 : ℝ) : ℂ) * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0 := by
      intro w hw
      rcases Finset.mem_insert.mp hw with h | h
      · rw [h]; exact ⟨hnorm γ hγa, hz⟩
      · rw [Finset.mem_singleton.mp h]
        exact ⟨hnorm (-γ) (by rwa [abs_neg]), hz'⟩
    have hsum : ∑ w ∈ ({ρ, ρ'} : Finset ℂ),
        (1 / (((1 + 60 * ε : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I - w)).re
        = 2 * ((60 * ε + δ) / ((60 * ε + δ) ^ 2 + γ ^ 2)) := by
      rw [Finset.sum_pair hne]
      have e1 : ((1 + 60 * ε : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I - ρ
          = ((60 * ε + δ : ℝ) : ℂ) + ((-γ : ℝ) : ℂ) * I := by rw [hρ]; push_cast; ring
      have e2 : ((1 + 60 * ε : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I - ρ'
          = ((60 * ε + δ : ℝ) : ℂ) + ((γ : ℝ) : ℂ) * I := by rw [hρ']; push_cast; ring
      rw [e1, e2, re_one_div, re_one_div, neg_sq]
      ring
    have hP : 60 * ε / ((60 * ε) ^ 2 + (0 : ℝ) ^ 2) ≤ 1 / (60 * ε) := by
      apply le_of_eq
      rw [show (60 * ε) ^ 2 + (0 : ℝ) ^ 2 = 60 * ε * (60 * ε) by ring, div_mul_eq_div_div,
        div_self ha0.ne']
    have e0 : ((1 + 60 * ε : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I = ((1 + 60 * ε : ℝ) : ℂ) := by
      push_cast; ring
    have hmain : 2 * ((60 * ε + δ) / ((60 * ε + δ) ^ 2 + γ ^ 2))
        ≤ 1 / (60 * ε) + 2 * (C * 𝓕.ell 0) := by
      by_cases h1 : χ = 1
      · have h0 := (GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity 𝓕 χ χ (1 + 60 * ε) 0 (by linarith)).2.1
        have hb := hR 𝓕 χ (60 * ε) 0 (1 / (60 * ε)) ha0 ha2 (by positivity) (fun _ => hP)
          {ρ, ρ'} hnear
        rw [hsum, e0, h1] at hb
        have hC0 : 0 ≤ C * 𝓕.ell 0 := mul_nonneg hC.le (by linarith [one_le_ell 𝓕 0])
        linarith
      · have h0 := ((GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity 𝓕 χ χ (1 + 60 * ε) 0 (by linarith)).2.2 hχ2 hχ2).1
        have hb1 := hR 𝓕 1 (60 * ε) 0 (1 / (60 * ε)) ha0 ha2 (by positivity) (fun _ => hP)
          ∅ (by simp)
        have hb2 := hR 𝓕 χ (60 * ε) 0 0 ha0 ha2 le_rfl (fun h => absurd h h1) {ρ, ρ'} hnear
        rw [hsum, e0] at hb2
        rw [e0, Finset.sum_empty] at hb1
        linarith
    have hlow : 60 / (4621 * ε) ≤ (60 * ε + δ) / ((60 * ε + δ) ^ 2 + γ ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ 60 * ε + δ - 60 * ε by linarith)
        (show (0 : ℝ) ≤ 61 * ε - (60 * ε + δ) by linarith), mul_pos hε hε]
    have i1 : 1 / (60 * ε) = v / 60 := by rw [hv]; ring
    have i2 : 60 / (4621 * ε) = 60 / 4621 * v := by rw [hv]; ring
    nlinarith
  · have hcase1 : χ = 1 → (30 * ε) ^ 2 ≤ γ ^ 2 := by
      intro h
      by_contra hc
      push_neg at hc
      exact hB ⟨by rw [h, mul_one], hc⟩
    have hcase2 : χ * χ = 1 → (30 * ε) ^ 2 ≤ (2 * γ) ^ 2 := by
      intro h
      have : (30 * ε) ^ 2 ≤ γ ^ 2 := by
        by_contra hc
        push_neg at hc
        exact hB ⟨h, hc⟩
      nlinarith [sq_nonneg γ]
    have ha0 : 0 < 6 * ε := by positivity
    have ha2 : 6 * ε ≤ 1 / 2 := by linarith
    have hP0 : 0 ≤ 1 / 156 * (1 / ε) := by positivity
    have hP1 : 6 * ε / ((6 * ε) ^ 2 + (0 : ℝ) ^ 2) ≤ 1 / (6 * ε) := by
      apply le_of_eq
      rw [show (6 * ε) ^ 2 + (0 : ℝ) ^ 2 = 6 * ε * (6 * ε) by ring, div_mul_eq_div_div,
        div_self ha0.ne']
    have h0 := (GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity 𝓕 χ χ (1 + 6 * ε) γ (by linarith)).1
    have hb1 := hR 𝓕 1 (6 * ε) 0 (1 / (6 * ε)) ha0 ha2 (by positivity) (fun _ => hP1) ∅ (by simp)
    have hρn : ∀ w ∈ ({ρ} : Finset ℂ), ‖w - (5 / 4 + γ * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0 := by
      intro w hw
      rw [Finset.mem_singleton.mp hw]
      refine ⟨?_, hz⟩
      have e : ρ - (5 / 4 + γ * I) = ((-(1 / 4 + δ) : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I := by
        rw [hρ]; push_cast; ring
      rw [e]
      refine (norm_ofReal_add_mul_I_le_abs_add_abs _ _).trans ?_
      rw [abs_neg, abs_of_nonneg (by linarith), abs_zero]
      linarith
    have hb2 := hR 𝓕 χ (6 * ε) γ (1 / 156 * (1 / ε)) ha0 ha2 hP0
      (fun h => pole_le hε (hcase1 h)) {ρ} hρn
    have hb3 := hR 𝓕 (χ * χ) (6 * ε) (2 * γ) (1 / 156 * (1 / ε)) ha0 ha2 hP0
      (fun h => pole_le hε (hcase2 h)) ∅ (by simp)
    have e0 : ((1 + 6 * ε : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I = ((1 + 6 * ε : ℝ) : ℂ) := by
      push_cast; ring
    have e2 : ((1 + 6 * ε : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * I
        = ((1 + 6 * ε : ℝ) : ℂ) + 2 * (γ : ℂ) * I := by push_cast; ring
    have e1 : ((1 + 6 * ε : ℝ) : ℂ) + (γ : ℂ) * I - ρ
        = ((6 * ε + δ : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I := by rw [hρ]; push_cast; ring
    rw [e0, Finset.sum_empty] at hb1
    rw [e2, Finset.sum_empty] at hb3
    rw [Finset.sum_singleton, e1, re_one_div] at hb2
    have hlow : 1 / (7 * ε) ≤ (6 * ε + δ) / ((6 * ε + δ) ^ 2 + (0 : ℝ) ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left (show 6 * ε + δ ≤ 7 * ε by linarith)
        (show (0 : ℝ) ≤ 6 * ε + δ by linarith)]
    have i1 : 1 / (6 * ε) = v / 6 := by rw [hv]; ring
    have i2 : 1 / (7 * ε) = v / 7 := by rw [hv]; ring
    have i3 : 1 / 156 * (1 / ε) = v / 156 := by rw [hv]; ring
    nlinarith

theorem zero_free_region : ∃ c : ℝ, 0 < c ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (s : ℂ), 3 / 4 ≤ s.re → 𝓕.F χ s = 0 → (χ * χ ≠ 1 ∨ s.im ≠ 0) → s.re < 1 - c / 𝓕.ell s.im := by
  obtain ⟨K, hK, hKb⟩ := inv_le_ell
  refine ⟨1 / (4 * K + 400), by positivity, ?_⟩
  intro 𝓕 χ s _ hs hχ
  by_contra hlt
  push_neg at hlt
  have hℓ2 := 𝓕.two_lt_ell s.im
  have hℓpos : 0 < 𝓕.ell s.im := by linarith
  have hpos : 0 < (2 * K + 200) * 𝓕.ell s.im := mul_pos (by linarith) hℓpos
  have hε : 0 < 1 / ((2 * K + 200) * 𝓕.ell s.im) := by positivity
  have hε1 : 1 / ((2 * K + 200) * 𝓕.ell s.im) ≤ 1 / 400 := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith [mul_pos hK hℓpos]
  have hδ : 0 ≤ 1 - s.re := by linarith [re_le_one hs]
  have hδε : 1 - s.re ≤ 1 / ((2 * K + 200) * 𝓕.ell s.im) := by
    have h1 : 1 - s.re ≤ 1 / (4 * K + 400) / 𝓕.ell s.im := by linarith
    refine h1.trans ?_
    rw [div_div]
    apply one_div_le_one_div_of_le hpos
    nlinarith [mul_pos hK hℓpos]
  have hz : 𝓕.F χ (((1 - (1 - s.re) : ℝ) : ℂ) + s.im * I) = 0 := by
    rw [show (1 - (1 - s.re) : ℝ) = s.re by ring, re_add_im]
    exact hs
  have h := hKb 𝓕 χ _ (1 - s.re) s.im hz hχ hε hε1 hδ hδε
  rw [one_div_one_div] at h
  nlinarith [mul_pos hK hℓpos]

end GlobalTheory.Hk.ZeroFree
