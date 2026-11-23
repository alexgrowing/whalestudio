import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AnalyticAtDslope
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionFamilyContinuationGrowth
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassFamilyLogDerivReGtOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivSubExceptionalLe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TruncatedPerronOfLeTwoVonMangoldt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumVonMangoldtLeTwoMul
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk.PsiExc

theorem shift (ψ : ℂ → ℂ) (S : Finset ℂ) (k : ℂ → ℂ) (u σ c T M : ℝ) (hu : 1 < u)
    (hσ : 1 / 2 ≤ σ) (hσc : σ < c) (hc3 : c ≤ 3) (huc : u ^ c ≤ 3 * u) (hT : 0 < T) (hM : 0 ≤ M)
    (hS : ∀ p ∈ S, σ < p.re ∧ p.re < c ∧ p.im = 0)
    (hd : ∀ s : ℂ, σ ≤ s.re → s.re ≤ c → |s.im| ≤ T → s ∉ S → DifferentiableAt ℂ ψ s)
    (hp : ∀ p ∈ S, ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧ ∀ᶠ s in 𝓝[≠] p, ψ s = k p / (s - p) + g s)
    (hb : ∀ s : ℂ, σ ≤ s.re → s.re ≤ c → |s.im| ≤ T → (s.re = σ ∨ |s.im| = T) → ‖ψ s‖ ≤ M) :
    ‖(1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
        -(ψ ((c : ℂ) + t * I)) * (u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))
      + ∑ p ∈ S, k p * ((u : ℂ) ^ p / p)‖ ≤ 18 * (M * u / T) + 4 * (T * M * u ^ σ) := by
  have hu0 : 0 < u := by linarith
  have key := GlobalTheory.ResRect.residue_rectangle
    (fun s => -(ψ s) * (u : ℂ) ^ s / s)
    ⟨σ, -T⟩ ⟨c, T⟩ S (fun p => -(k p * ((u : ℂ) ^ p / p))) hσc (by simp only; linarith)
    (fun p hp => by
      obtain ⟨h1, h2, h3⟩ := hS p hp
      simp only [h3]
      exact ⟨h1, h2, by linarith, hT⟩)
    (by
      rintro s ⟨hs, hsS⟩
      simp only [mem_reProdIm, Set.mem_Icc] at hs
      have hs0 : s ≠ 0 := by
        rintro rfl
        have := hs.1.1
        simp only [zero_re] at this
        linarith
      exact (((hd s hs.1.1 hs.1.2 (abs_le.2 hs.2) hsS).neg.mul
        (GlobalTheory.ExplicitRect.analyticAt_cpow hu0 s).differentiableAt).div differentiableAt_id
        hs0).differentiableWithinAt)
    (fun p hpS => by
      obtain ⟨g, hg, hφ⟩ := hp p hpS
      have hp0 : p ≠ 0 := by
        rintro rfl
        have := (hS _ hpS).1
        simp only [zero_re] at this
        linarith
      exact GlobalTheory.ExplicitRect.expand_simple hu0 hp0 hg hφ)
  simp only [Finset.sum_neg_distrib] at key
  have hor : ∀ τ : ℝ, |τ| = T → ‖∫ x : ℝ in σ..c,
      (-(ψ ((x : ℂ) + τ * I)) * (u : ℂ) ^ ((x : ℂ) + τ * I) / ((x : ℂ) + τ * I))‖
      ≤ 9 * (M * u / T) := by
    intro τ hτ
    have key := intervalIntegral.norm_integral_le_of_norm_le_const (a := σ) (b := c)
      (C := 3 * (M * u / T))
      (f := fun x : ℝ => (-(ψ ((x : ℂ) + τ * I)) * (u : ℂ) ^ ((x : ℂ) + τ * I) / ((x : ℂ) + τ * I)))
      (by
        intro x hx
        rw [Set.uIoc_of_le hσc.le] at hx
        have h1 := hb ((x : ℂ) + τ * I) (by simpa using hx.1.le) (by simpa using hx.2)
          (by simpa using hτ.le) (Or.inr (by simpa using hτ))
        have h2 : ‖(u : ℂ) ^ ((x : ℂ) + τ * I)‖ ≤ 3 * u := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0]
          simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
            add_zero]
          exact (Real.rpow_le_rpow_of_exponent_le hu.le hx.2).trans huc
        have h3 : T ≤ ‖(x : ℂ) + τ * I‖ := by
          rw [← hτ]
          have := Complex.abs_im_le_norm ((x : ℂ) + τ * I)
          simpa using this
        rw [norm_div, norm_mul, norm_neg]
        calc _ ≤ M * (3 * u) / T := by gcongr
          _ = _ := by ring)
    refine key.trans ?_
    have : |c - σ| ≤ 3 := by rw [abs_le]; constructor <;> linarith
    have h4 : 0 ≤ M * u / T := by positivity
    nlinarith
  have left : ‖∫ t : ℝ in (-T)..T,
      (-(ψ ((σ : ℂ) + t * I)) * (u : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I))‖
      ≤ 4 * (T * M * u ^ σ) := by
    have key := intervalIntegral.norm_integral_le_of_norm_le_const (a := -T) (b := T)
      (C := 2 * (M * u ^ σ))
      (f := fun t : ℝ => (-(ψ ((σ : ℂ) + t * I)) * (u : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I)))
      (by
        intro t ht
        rw [Set.uIoc_of_le (by linarith)] at ht
        have h1 := hb ((σ : ℂ) + t * I) (by simp) (by simpa using hσc.le)
          (by simpa using abs_le.2 ⟨ht.1.le, ht.2⟩) (Or.inl (by simp))
        have h2 : ‖(u : ℂ) ^ ((σ : ℂ) + t * I)‖ = u ^ σ := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0]
          simp
        have h3 : 1 / 2 ≤ ‖(σ : ℂ) + t * I‖ := by
          have := Complex.re_le_norm ((σ : ℂ) + t * I)
          exact hσ.trans (by simpa using this)
        rw [norm_div, norm_mul, norm_neg, h2]
        calc _ ≤ M * u ^ σ / (1 / 2) := by gcongr
          _ = _ := by ring)
    refine key.trans (le_of_eq ?_)
    rw [abs_of_pos (by linarith)]
    ring
  have gen : ∀ a b v l Z : ℂ, a - b + I * v - I * l = 2 * Real.pi * I * (-Z) →
      ‖(1 / (2 * Real.pi) : ℂ) * v + Z‖ ≤ ‖a‖ + ‖b‖ + ‖l‖ := by
    intro a b v l Z e
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have e2 : (1 / (2 * Real.pi) : ℂ) * v + Z
        = (1 / (2 * Real.pi) : ℂ) * (I * a - I * b + l) := by
      field_simp
      linear_combination (-I) * e + (v - l + 2 * Real.pi * Z) * I_mul_I
    have n1 : ‖(1 / (2 * Real.pi) : ℂ)‖ ≤ 1 := by
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, norm_one,
        Complex.norm_ofNat, div_le_one (by positivity)]
      linarith [Real.pi_gt_three]
    have n2 : ‖I * a - I * b + l‖ ≤ ‖a‖ + ‖b‖ + ‖l‖ := by
      refine (norm_add_le _ _).trans ?_
      have := norm_sub_le (I * a) (I * b)
      simp only [norm_mul, norm_I, one_mul] at this
      linarith
    rw [e2, norm_mul]
    have := mul_le_mul n1 n2 (norm_nonneg _) zero_le_one
    linarith
  refine (gen _ _ _ _ _ key).trans ?_
  have a1 := hor (-T) (by rw [abs_neg, abs_of_pos hT])
  have a2 := hor T (abs_of_pos hT)
  linarith

theorem norm_lamChi_le (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (n : ℕ) : ‖𝓕.lamChi χ n‖ ≤ 2 * Λ n := by
  refine le_trans ?_ (𝓕.lam_le n)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun g _ => ?_)
  rw [norm_mul, AddChar.norm_apply, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (𝓕.lam_nonneg g n)]

theorem one_le_ell (𝓕 : LFam) (t : ℝ) : 1 ≤ 𝓕.ell t := by
  rw [LFam.ell, Real.le_log_iff_exp_le (by have := 𝓕.B_ge; positivity)]
  have := Real.exp_one_lt_d9
  have := 𝓕.B_ge
  nlinarith [abs_nonneg t]

theorem ell_mono (𝓕 : LFam) {t T : ℝ} (h : |t| ≤ T) : 𝓕.ell t ≤ 𝓕.ell T := by
  have := 𝓕.B_ge
  refine Real.log_le_log (by positivity) ?_
  have h2 : |t| + 2 ≤ |T| + 2 := by linarith [le_abs_self T]
  exact mul_le_mul_of_nonneg_left h2 (by linarith)

theorem norm_term_le {u β σ : ℝ} (hu : 1 ≤ u) (h1 : 1 / 2 ≤ β) (h2 : β ≤ σ) :
    ‖(u : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤ 2 * u ^ σ := by
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), ofReal_re, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by linarith)]
  have := Real.rpow_le_rpow_of_exponent_le hu h2
  calc _ ≤ u ^ σ / (1 / 2) := by gcongr
    _ = _ := by ring

theorem norm_sum_le_of_card {Z : Finset ℝ} (hZ : Z.card ≤ 1) {f : ℝ → ℂ} {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ β ∈ Z, ‖f β‖ ≤ b) : ‖∑ β ∈ Z, f β‖ ≤ b := by
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ b h).trans ?_)
  have : (Z.card : ℝ) ≤ 1 := by exact_mod_cast hZ
  rw [nsmul_eq_mul]
  nlinarith

theorem exists_line {Z : Finset ℝ} (hZ : Z.card ≤ 1) {d : ℝ} (hd : 0 < d) :
    ∃ σ : ℝ, 1 - 4 * d ≤ σ ∧ σ ≤ 1 - 2 * d ∧ ∀ β ∈ Z, d ≤ |σ - β| := by
  rcases Z.eq_empty_or_nonempty with rfl | ⟨β, hβ⟩
  · exact ⟨1 - 2 * d, by linarith, le_rfl, by simp⟩
  have e : ∀ γ ∈ Z, γ = β := fun γ hγ => Finset.card_le_one.1 hZ _ hγ _ hβ
  rcases le_total β (1 - 3 * d) with h | h
  · refine ⟨1 - 2 * d, by linarith, le_rfl, fun γ hγ => ?_⟩
    rw [e γ hγ]
    exact le_abs.2 (Or.inl (by linarith))
  · refine ⟨1 - 4 * d, le_rfl, by linarith, fun γ hγ => ?_⟩
    rw [e γ hγ]
    exact le_abs.2 (Or.inr (by linarith))

theorem logDeriv_simple {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p) (h0 : f p = 0)
    (h1 : deriv f p ≠ 0) : ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧ ∀ᶠ s in 𝓝[≠] p,
      deriv f s / f s = 1 / (s - p) + g s := by
  have ho : analyticOrderAt f p = 1 := hf.analyticOrderAt_eq_one_of_zero_deriv_ne_zero h0 h1
  obtain ⟨g, hg, h⟩ := GlobalTheory.ExplicitRect.logDeriv_pole hf (by rw [ho]; simp)
  refine ⟨g, hg, ?_⟩
  simpa [analyticOrderNatAt, ho] using h

theorem contour (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (Z : Finset ℝ) (c₀ C u T d : ℝ) (hc₀ : 0 < c₀)
    (hc₁ : c₀ ≤ 1 / 20) (hC : 0 < C) (hZ : 𝓕.ExcZ χ c₀ Z) (hu : 2 ≤ u) (hT : 1 ≤ T)
    (hd : d = c₀ / (8 * 𝓕.ell T))
    (hb : ∀ s : ℂ, 1 - c₀ / 2 / 𝓕.ell s.im ≤ s.re → s.re ≤ 3 → (∀ β ∈ Z, s ≠ (β : ℂ)) →
      ‖deriv (𝓕.F χ) s / 𝓕.F χ s - ∑ β ∈ Z, 1 / (s - (β : ℂ))‖ ≤ C * 𝓕.ell s.im ^ 2) :
    ‖(1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
        LSeries (𝓕.lamChi χ) (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I) *
          (u : ℂ) ^ (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I) /
          (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I))
      - (if χ = 1 then (u : ℂ) else 0) + ∑ β ∈ Z, (u : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤
      18 * ((C * 𝓕.ell T ^ 2 + 2 / d) * u / T) + 4 * (T * (C * 𝓕.ell T ^ 2 + 2 / d) * u ^ (1 - 2 * d))
        + 2 * u ^ (1 - 2 * d) := by
  have hu0 : 0 < u := by linarith
  have hlog : 1 / 2 < Real.log u := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num) hu
    linarith
  have hc1 : 1 < 1 + 1 / Real.log u := by
    have : 0 < 1 / Real.log u := by apply one_div_pos.2; linarith
    linarith
  have hc3 : 1 + 1 / Real.log u ≤ 3 := by
    have : 1 / Real.log u ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  have huc : u ^ (1 + 1 / Real.log u) ≤ 3 * u := by
    rw [Real.rpow_add hu0, Real.rpow_one, Real.rpow_def_of_pos hu0,
      mul_one_div_cancel (by linarith)]
    have := Real.exp_one_lt_d9
    nlinarith
  generalize 1 + 1 / Real.log u = c at *
  obtain ⟨hcard, hZ1, hZ2⟩ := hZ
  have hl := one_le_ell 𝓕 T
  have hd0 : 0 < d := by rw [hd]; positivity
  have hd1 : d ≤ 1 / 160 := by
    rw [hd, div_le_iff₀ (by positivity)]; linarith
  obtain ⟨σ, hσ1, hσ2, hσ3⟩ := exists_line hcard hd0
  have hβ : ∀ β ∈ Z, 1 / 2 ≤ β := fun β h => by
    have h1 := (hZ1 β h).1
    have h2 : c₀ / 𝓕.ell 0 ≤ c₀ := div_le_self hc₀.le (one_le_ell 𝓕 0)
    linarith
  have hreg : ∀ s : ℂ, σ ≤ s.re → |s.im| ≤ T → 1 - c₀ / 2 / 𝓕.ell s.im ≤ s.re := by
    intro s h1 h2
    have h3 := ell_mono 𝓕 h2
    have h4 := one_le_ell 𝓕 s.im
    have h5 : c₀ / 2 / 𝓕.ell T ≤ c₀ / 2 / 𝓕.ell s.im := by gcongr
    have h6 : c₀ / 2 / 𝓕.ell T = 4 * d := by rw [hd]; field_simp; ring
    linarith
  have hreg' : ∀ s : ℂ, σ ≤ s.re → |s.im| ≤ T → 1 - c₀ / 𝓕.ell s.im ≤ s.re := by
    intro s h1 h2
    have h3 := hreg s h1 h2
    have h4 := one_le_ell 𝓕 s.im
    have h5 : c₀ / 2 / 𝓕.ell s.im ≤ c₀ / 𝓕.ell s.im := by gcongr; linarith
    linarith
  have han : ∀ s : ℂ, σ ≤ s.re → AnalyticAt ℂ (𝓕.F χ) s := fun s hs =>
    (GlobalTheory.Hk.RayCont.continuation_growth 𝓕 χ).1 s (by simp only [Set.mem_setOf_eq]; linarith)
  set Z' := Z.filter (fun β => σ < β) with hZ'
  have h1Z : (1 : ℂ) ∉ Z'.image (fun β : ℝ => (β : ℂ)) := by
    intro h
    obtain ⟨β, h1, h2⟩ := Finset.mem_image.1 h
    have h3 : β = 1 := by exact_mod_cast h2
    have := (hZ1 β (Finset.mem_filter.1 h1).1).2.1
    linarith
  have hM : 0 ≤ C * 𝓕.ell T ^ 2 + 2 / d := by positivity
  have hite : ∀ s : ℂ, s ≠ 1 →
      AnalyticAt ℂ (fun s : ℂ => if χ = 1 then 1 / (s - 1) else (0 : ℂ)) s := by
    intro s hs
    by_cases h : χ = 1
    · simp only [if_pos h]
      exact analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.2 hs)
    · simp only [if_neg h]
      exact analyticAt_const
  have key := shift
    (fun s => deriv (𝓕.F χ) s / 𝓕.F χ s - (if χ = 1 then 1 / (s - 1) else 0))
    (insert 1 (Z'.image (fun β : ℝ => (β : ℂ))))
    (fun p => if p = 1 then (if χ = 1 then -1 else 0) else 1) u σ c T _ (by linarith) (by linarith)
    (by linarith) hc3 huc (by linarith) hM ?_ ?_ ?_ ?_
  · have e1 : ∀ t : ℝ, -(deriv (𝓕.F χ) ((c : ℂ) + t * I) / 𝓕.F χ ((c : ℂ) + t * I) -
        (if χ = 1 then 1 / (((c : ℂ) + t * I) - 1) else 0)) =
        LSeries (𝓕.lamChi χ) ((c : ℂ) + t * I) := fun t => by
      rw [← (GlobalTheory.Hk.LogDeriv.logDeriv_F 𝓕 χ _ (by simpa using hc1)).2.2.2]
      ring
    simp only [e1] at key
    rw [Finset.sum_insert h1Z, Finset.sum_image (fun a _ b _ h => ofReal_injective h)] at key
    have e2 : ∑ β ∈ Z', (if (β : ℂ) = 1 then (if χ = 1 then -1 else 0) else 1) *
        ((u : ℂ) ^ (β : ℂ) / (β : ℂ)) = ∑ β ∈ Z', (u : ℂ) ^ (β : ℂ) / (β : ℂ) :=
      Finset.sum_congr rfl fun β h => by
        have hne : (β : ℂ) ≠ 1 := fun e => h1Z (Finset.mem_image.2 ⟨β, h, e⟩)
        rw [if_neg hne, one_mul]
    have e3 : (if (1 : ℂ) = 1 then (if χ = 1 then -1 else 0) else 1) *
        ((u : ℂ) ^ (1 : ℂ) / (1 : ℂ)) = -(if χ = 1 then (u : ℂ) else 0) := by
      split_ifs <;> simp_all
    rw [e2, e3] at key
    have hs : u ^ σ ≤ u ^ (1 - 2 * d) := Real.rpow_le_rpow_of_exponent_le (by linarith) hσ2
    have n1 : ‖∑ β ∈ Z.filter (fun β => ¬ σ < β), (u : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤
        2 * u ^ (1 - 2 * d) :=
      norm_sum_le_of_card ((Finset.card_filter_le _ _).trans hcard) (by positivity) fun β h =>
        norm_term_le (by linarith) (hβ β (Finset.mem_filter.1 h).1)
          ((not_lt.1 (Finset.mem_filter.1 h).2).trans hσ2)
    rw [← Finset.sum_filter_add_sum_filter_not Z (fun β => σ < β), ← add_assoc]
    refine (norm_add_le _ _).trans (add_le_add ?_ n1)
    rw [sub_eq_add_neg, add_assoc]
    refine key.trans ?_
    gcongr
  · intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    · simp only [one_re, one_im]
      exact ⟨by linarith, hc1, trivial⟩
    · obtain ⟨β, h1, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨h2, h3⟩ := Finset.mem_filter.1 h1
      have := (hZ1 β h2).2.1
      simp only [ofReal_re, ofReal_im]
      exact ⟨h3, by linarith, trivial⟩
  · intro s h1 h2 h3 h4
    rw [Finset.mem_insert, not_or] at h4
    have hF : 𝓕.F χ s ≠ 0 := fun h0 => by
      obtain ⟨β, h5, rfl⟩ := hZ2 s (hreg' s h1 h3) h0
      refine h4.2 (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨h5, lt_of_le_of_ne h1 ?_⟩))
      intro e
      have := hσ3 β h5
      rw [e] at this
      simp at this
      linarith
    exact (((han s h1).deriv.div (han s h1) hF).sub (hite s h4.1)).differentiableAt
  · intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    · have h1 : σ ≤ (1 : ℂ).re := by simp only [one_re]; linarith
      have hF : 𝓕.F χ 1 ≠ 0 := fun h0 => by
        obtain ⟨β, h5, h6⟩ := hZ2 1 (hreg' 1 h1 (by simp; linarith)) h0
        have h3 : (1 : ℝ) = β := by exact_mod_cast h6
        have := (hZ1 β h5).2.1
        linarith
      refine ⟨_, (han 1 h1).deriv.div (han 1 h1) hF, Eventually.of_forall fun s => ?_⟩
      simp only [if_true, Pi.div_apply]
      split_ifs <;> ring
    · have hp1 : p ≠ 1 := fun e => h1Z (e ▸ hp)
      obtain ⟨β, h1, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨h2, h3⟩ := Finset.mem_filter.1 h1
      obtain ⟨g, hg, h⟩ := logDeriv_simple (han β h3.le) (hZ1 β h2).2.2.1 (hZ1 β h2).2.2.2
      refine ⟨_, hg.sub (hite _ hp1), h.mono fun s hs => ?_⟩
      simp only [if_neg hp1, Pi.sub_apply, hs]
      ring
  · intro s h1 h2 h3 h4
    have far : ∀ x : ℝ, d ≤ |σ - x| → d ≤ ‖s - (x : ℂ)‖ := by
      intro x hx
      rcases h4 with h4 | h4
      · refine hx.trans ?_
        have := Complex.abs_re_le_norm (s - (x : ℂ))
        simpa [h4] using this
      · have := Complex.abs_im_le_norm (s - (x : ℂ))
        simp only [sub_im, ofReal_im, sub_zero, h4] at this
        linarith
    have inv : ∀ x : ℝ, d ≤ |σ - x| → ‖1 / (s - (x : ℂ))‖ ≤ 1 / d := by
      intro x hx
      rw [norm_div, norm_one]
      exact one_div_le_one_div_of_le hd0 (far x hx)
    have b1 := hb s (hreg s h1 h3) (h2.trans hc3) fun β h e => by
      have := far β (hσ3 β h)
      rw [e] at this
      simp at this
      linarith
    have b2 : ‖∑ β ∈ Z, 1 / (s - (β : ℂ))‖ ≤ 1 / d :=
      norm_sum_le_of_card hcard (by positivity) fun β h => inv β (hσ3 β h)
    have b3 : ‖(if χ = 1 then 1 / (s - 1) else 0 : ℂ)‖ ≤ 1 / d := by
      split_ifs
      · simpa using inv 1 (le_abs.2 (Or.inr (by linarith)))
      · simp [hd0.le]
    have b4 : C * 𝓕.ell s.im ^ 2 ≤ C * 𝓕.ell T ^ 2 := by
      have := ell_mono 𝓕 h3
      have := one_le_ell 𝓕 s.im
      gcongr
    have b5 := norm_sub_le (deriv (𝓕.F χ) s / 𝓕.F χ s) (if χ = 1 then 1 / (s - 1) else 0 : ℂ)
    have b6 := norm_add_le (deriv (𝓕.F χ) s / 𝓕.F χ s - ∑ β ∈ Z, 1 / (s - (β : ℂ)))
      (∑ β ∈ Z, 1 / (s - (β : ℂ)))
    rw [sub_add_cancel] at b6
    have b7 : 2 / d = 1 / d + 1 / d := by ring
    linarith

theorem norm_psi_le (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {u : ℝ} (hu : 0 ≤ u) : ‖𝓕.psi χ u‖ ≤ 4 * u := by
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun n _ => norm_lamChi_le 𝓕 χ n).trans ?_)
  rw [← Finset.mul_sum]
  have := GlobalTheory.Mem.An.sum_vonMangoldt_le_two_mul u hu
  linarith

theorem pow_four_mul_exp_le {δ W : ℝ} (hδ : 0 < δ) (hW : 0 ≤ W) :
    W ^ 4 * Real.exp (-(δ * W)) ≤ 24 * (2 / δ) ^ 4 * Real.exp (-(δ / 2) * W) := by
  have h := Real.pow_div_factorial_le_exp (δ / 2 * W) (by positivity) 4
  have e : Real.exp (-(δ / 2) * W) = Real.exp (δ / 2 * W) * Real.exp (-(δ * W)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e, ← mul_assoc]
  gcongr
  have e2 : W ^ 4 = 24 * (2 / δ) ^ 4 * ((δ / 2 * W) ^ 4 / (Nat.factorial 4 : ℕ)) := by
    simp only [Nat.factorial]
    field_simp
    norm_num
  rw [e2]
  gcongr

theorem const_le {c₀ C l W : ℝ} (hc₀ : 0 < c₀) (hC : 0 < C) (hl1 : 1 ≤ l) (hl : l ≤ 3 * W)
    (hW1 : 1 ≤ W) : C * l ^ 2 + 2 / (c₀ / (8 * l)) ≤ (9 * C + 48 / c₀) * W ^ 4 := by
  have h1 : l ^ 2 ≤ (3 * W) ^ 2 := by gcongr
  have h2 : W ^ 2 ≤ W ^ 4 := pow_le_pow_right₀ hW1 (by norm_num)
  have h3 : W ≤ W ^ 4 := le_self_pow₀ hW1 (by norm_num)
  have h4 : 2 / (c₀ / (8 * l)) = 48 / c₀ * (l / 3) := by field_simp; norm_num
  have h5 : 48 / c₀ * (l / 3) ≤ 48 / c₀ * W ^ 4 := by gcongr; linarith
  have h6 : C * l ^ 2 ≤ C * (9 * W ^ 4) := by gcongr; linarith
  rw [h4]
  linarith

theorem rpow_le {c₀ u l W : ℝ} (hc₀ : 0 < c₀) (hu0 : 0 < u) (hl1 : 1 ≤ l) (hl : l ≤ 3 * W)
    (hW0 : 0 ≤ W) (hW2 : W ^ 2 = Real.log u) :
    u ^ (1 - 2 * (c₀ / (8 * l))) ≤ u / Real.exp (c₀ / 32 * W) / Real.exp (c₀ / 32 * W) := by
  rw [Real.rpow_sub hu0, Real.rpow_one, div_div, ← Real.exp_add, Real.rpow_def_of_pos hu0,
    ← hW2]
  gcongr
  have e : W ^ 2 * (2 * (c₀ / (8 * l))) = c₀ / 4 * W * W / l := by field_simp; ring
  rw [e, le_div_iff₀ (by linarith)]
  have := mul_le_mul_of_nonneg_left hl (mul_nonneg hc₀.le hW0)
  nlinarith [mul_nonneg (mul_nonneg hc₀.le hW0) hW0]

theorem total_le {δ P K M Y u T W : ℝ} (hδ0 : 0 < δ) (hP : 0 < P) (hK0 : 0 < K) (hM0 : 0 ≤ M)
    (hu0 : 0 < u) (hW1 : 1 ≤ W) (hW2 : W ^ 2 = Real.log u) (hT : T = Real.exp (δ * W))
    (hT2 : 2 ≤ T) (hTu : T ≤ u) (hM : M ≤ K * W ^ 4) (hpow : Y ≤ u / T / T) :
    P * (u * Real.log u ^ 2 / T + Real.log u) + (18 * (M * u / T) + 4 * (T * M * Y) + 2 * Y) ≤
      (14 + (2 * P + 22 * K + 2) * (24 * (2 / δ) ^ 4)) * u * Real.exp (-(δ / 2) * W) := by
  have hW0 : 0 ≤ W := by linarith
  have hE := Real.exp_pos (-(δ / 2) * W)
  have hT0 : 0 < T := by linarith
  have hR1 : 1 ≤ u / T := (one_le_div hT0).2 hTu
  have hW4 : 1 ≤ W ^ 4 := one_le_pow₀ hW1
  have t1 : M * u / T ≤ K * (W ^ 4 * (u / T)) := by
    rw [mul_div_assoc, ← mul_assoc]; gcongr
  have t2 : T * M * Y ≤ K * (W ^ 4 * (u / T)) := by
    calc T * M * Y ≤ T * (K * W ^ 4) * (u / T / T) := by
          rcases le_total 0 Y with hY | hY
          · gcongr
          · exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) hY).trans (by positivity)
      _ = _ := by field_simp
  have t3 : Y ≤ W ^ 4 * (u / T) := by
    refine hpow.trans ((div_le_self (by positivity) (by linarith)).trans ?_)
    nlinarith
  have t4 : u * Real.log u ^ 2 / T + Real.log u ≤ 2 * (W ^ 4 * (u / T)) := by
    have h2 : W ^ 2 ≤ W ^ 4 := pow_le_pow_right₀ hW1 (by norm_num)
    have e : u * Real.log u ^ 2 / T = W ^ 4 * (u / T) := by rw [← hW2]; ring
    rw [e, ← hW2]
    nlinarith
  have t5 : W ^ 4 * (u / T) ≤ 24 * (2 / δ) ^ 4 * (u * Real.exp (-(δ / 2) * W)) := by
    have := mul_le_mul_of_nonneg_left (pow_four_mul_exp_le hδ0 hW0) hu0.le
    rw [Real.exp_neg, ← hT] at this
    calc _ = u * (W ^ 4 * T⁻¹) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have t6 := mul_le_mul_of_nonneg_left t4 hP.le
  have t7 := mul_le_mul_of_nonneg_left t5 (by positivity : 0 ≤ 2 * P + 22 * K + 2)
  have t8 := mul_pos hu0 hE
  generalize W ^ 4 * (u / T) = R at *
  calc _ ≤ (2 * P + 22 * K + 2) * R := by linarith
    _ ≤ _ := by linarith

theorem psi_exceptional : ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ 1 / 20 → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (Z : Finset ℝ) (u : ℝ), 𝓕.ExcZ χ c₀ Z → 2 ≤ u → Real.log 𝓕.B ≤ Real.sqrt (Real.log u) → ‖𝓕.psi χ u - (if χ = 1 then (u : ℂ) else 0) + ∑ β ∈ Z, (u : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤ C * u * Real.exp (-c * Real.sqrt (Real.log u)) := by
  intro c₀ hc₀ hc₁
  obtain ⟨C, hC, H⟩ := GlobalTheory.Hk.LogDerivHalf.logDeriv_sub_exceptional_le c₀ hc₀ hc₁
  obtain ⟨P, hP, HP⟩ := GlobalTheory.PerronCoeff.truncated_perron_of_le_two_vonMangoldt
  set δ := c₀ / 32 with hδ
  have hδ0 : 0 < δ := by positivity
  set K := 9 * C + 48 / c₀ with hK
  have hK0 : 0 < K := by positivity
  refine ⟨δ / 2, 14 + (2 * P + 22 * K + 2) * (24 * (2 / δ) ^ 4), by positivity, by positivity, ?_⟩
  intro 𝓕 χ Z u hZ hu hB
  have hu0 : 0 < u := by linarith
  have hlog : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  have hW2 : Real.sqrt (Real.log u) ^ 2 = Real.log u := Real.sq_sqrt hlog
  have hW0 : 0 ≤ Real.sqrt (Real.log u) := Real.sqrt_nonneg _
  generalize Real.sqrt (Real.log u) = W at *
  have hE := Real.exp_pos (-(δ / 2) * W)
  have hQ : 0 ≤ (2 * P + 22 * K + 2) * (24 * (2 / δ) ^ 4) := by positivity
  rcases le_total (δ * W) 1 with h | h
  · have n1 := norm_psi_le 𝓕 χ hu0.le
    have n2 : ‖(if χ = 1 then (u : ℂ) else 0)‖ ≤ u := by
      split_ifs
      · simp [abs_of_pos hu0]
      · simp [hu0.le]
    have n3 : ‖∑ β ∈ Z, (u : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤ 2 * u :=
      norm_sum_le_of_card hZ.1 (by positivity) fun β hβ => by
        have h1 := (hZ.2.1 β hβ).1
        have h2 : c₀ / 𝓕.ell 0 ≤ c₀ := div_le_self hc₀.le (one_le_ell 𝓕 0)
        simpa using norm_term_le (u := u) (β := β) (σ := 1) (by linarith) (by linarith)
          (hZ.2.1 β hβ).2.1.le
    have n4 := norm_sub_le (𝓕.psi χ u) (if χ = 1 then (u : ℂ) else 0)
    refine (norm_add_le _ _).trans ?_
    have n5 := Real.add_one_le_exp (-(δ / 2) * W)
    have n6 : 1 / 2 ≤ Real.exp (-(δ / 2) * W) := by linarith
    have n7 := mul_le_mul_of_nonneg_left n6 hu0.le
    have n8 := mul_nonneg hQ (mul_pos hu0 hE).le
    nlinarith
  have hδ1 : δ ≤ 1 := by linarith
  have hW1 : 1 ≤ W := by nlinarith
  set T := Real.exp (δ * W) with hT
  have hT2 : 2 ≤ T := by
    have := Real.add_one_le_exp (δ * W)
    linarith
  have hTu : T ≤ u := by
    rw [hT, ← Real.le_log_iff_exp_le hu0, ← hW2]
    nlinarith
  have hl1 := one_le_ell 𝓕 T
  have hl : 𝓕.ell T ≤ 3 * W := by
    have hB4 := 𝓕.B_ge
    have e : 𝓕.ell T ≤ Real.log (𝓕.B * (2 * T)) := by
      refine Real.log_le_log (by positivity) ?_
      rw [abs_of_pos (by linarith)]
      gcongr
      linarith
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      hT, Real.log_exp] at e
    have := Real.log_two_lt_d9
    nlinarith
  have A := HP (𝓕.lamChi χ) u T (norm_lamChi_le 𝓕 χ) hT2 hTu
  have B := contour 𝓕 χ Z c₀ C u T _ hc₀ hc₁ hC hZ hu (by linarith) rfl (H 𝓕 χ Z hZ)
  have gen : ∀ a v m z : ℂ, ‖a - m + z‖ ≤ ‖a - v‖ + ‖v - m + z‖ := fun a v m z => by
    refine le_trans (le_of_eq ?_) (norm_add_le _ _)
    congr 1; ring
  refine ((gen _ _ _ _).trans (add_le_add A B)).trans ?_
  exact total_le hδ0 hP hK0 (by positivity) hu0 hW1 hW2 hT hT2 hTu (const_le hc₀ hC hl1 hl hW1)
    (rpow_le hc₀ hu0 hl1 hl hW0 hW2)

end GlobalTheory.Hk.PsiExc
