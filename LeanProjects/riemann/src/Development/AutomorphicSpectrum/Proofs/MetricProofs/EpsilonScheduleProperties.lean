import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.RegGlue
import ReciprocityTheory.AnalyticForms.LeviForms.RegChartC
import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LoglogQuotNonneg
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem log_div_self_anti (a b : ℝ) (ha : Real.exp 1 ≤ a) (hab : a ≤ b) :
    Real.log b / b ≤ Real.log a / a :=
  Real.log_div_self_antitoneOn ha (show Real.exp 1 ≤ b from ha.trans hab) hab

theorem epsT_mono (C t t' : ℝ) (hC : 0 ≤ C) (ht : 0 < t) (htt : t ≤ t')
    (ht' : t' ≤ Real.exp (-Real.exp 1)) : epsT C t ≤ epsT C t' := by
  have ht'0 : 0 < t' := ht.trans_le htt
  have h1 := (GlobalTheory.CompanionTheory.Ar.Giv.log_inv_bounds ht'0 ht').1
  have h2 : Real.log (1 / t') ≤ Real.log (1 / t) := by
    rw [one_div, one_div, Real.log_inv, Real.log_inv]
    linarith [Real.log_le_log ht htt]
  rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul]
  exact mul_le_mul_of_nonneg_left (log_div_self_anti _ _ h1 h2) hC

theorem le_epsT (C t : ℝ) (hC : 1 ≤ C) (ht : 0 < t) (hte : t ≤ Real.exp (-Real.exp 1)) :
    t ≤ epsT C t := by
  obtain ⟨h1, h2⟩ := GlobalTheory.CompanionTheory.Ar.Giv.log_inv_bounds ht hte
  set ℓ := Real.log (1 / t) with hℓ
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le (Real.exp_pos 1) h1
  have hle : ℓ ≤ 1 / t := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 / t by positivity)
    linarith
  have htl : t * ℓ ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hle ht.le
    rwa [mul_one_div_cancel ht.ne'] at this
  have hA : t ≤ 1 / ℓ := by rw [le_div_iff₀ hℓ0]; exact htl
  have hB : 1 / ℓ ≤ Real.log ℓ / ℓ := div_le_div_of_nonneg_right h2 hℓ0.le
  have hq : 0 ≤ Real.log ℓ / ℓ := div_nonneg (by linarith) hℓ0.le
  have hC' : Real.log ℓ / ℓ ≤ C * (Real.log ℓ / ℓ) := le_mul_of_one_le_left hq hC
  rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul]
  linarith

theorem epsT_tendsto (C : ℝ) : Tendsto (epsT C) (𝓝[>] 0) (𝓝 0) := by
  have hl : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa using this
  have hL : Tendsto (fun t : ℝ => Real.log (1 / t)) (𝓝[>] 0) atTop := by
    have := Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
    simpa [Function.comp_def, one_div] using this
  have h := (hl.comp hL).const_mul C
  rw [mul_zero] at h
  have e : epsT C = fun t => C * ((fun x : ℝ => Real.log x / x) ∘ (fun t : ℝ => Real.log (1 / t))) t := by
    funext t
    rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul]
    rfl
  rw [e]
  exact h

theorem epsT_le_one (C : ℝ) : ∃ a : ℝ, 0 < a ∧ ∀ t, 0 < t → t ≤ a → epsT C t ≤ 1 := by
  have hev : {t : ℝ | epsT C t < 1} ∈ 𝓝[>] (0 : ℝ) :=
    (epsT_tendsto C) (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hu0 : (0 : ℝ) < u := hu
  refine ⟨u / 2, by linarith, fun t ht hta => ?_⟩
  exact (hsub ⟨ht, by linarith⟩ : epsT C t < 1).le

theorem fin_pos_lower (n : ℕ) (a : Fin n → ℝ) (ha : ∀ j, 0 < a j) :
    ∃ b : ℝ, 0 < b ∧ ∀ j, b ≤ a j := by
  by_cases h : Nonempty (Fin n)
  · refine ⟨Finset.univ.inf' Finset.univ_nonempty a,
      (Finset.lt_inf'_iff _).2 (fun j _ => ha j), fun j => Finset.inf'_le _ (Finset.mem_univ j)⟩
  · exact ⟨1, one_pos, fun j => (h ⟨j⟩).elim⟩

theorem epsT_numerics :
    (∀ a b : ℝ, Real.exp 1 ≤ a → a ≤ b → Real.log b / b ≤ Real.log a / a) ∧
    (∀ C t t' : ℝ, 0 ≤ C → 0 < t → t ≤ t' → t' ≤ Real.exp (-Real.exp 1) → epsT C t ≤ epsT C t') ∧
    (∀ C t : ℝ, 1 ≤ C → 0 < t → t ≤ Real.exp (-Real.exp 1) → t ≤ epsT C t) ∧
    (∀ C : ℝ, Tendsto (epsT C) (𝓝[>] 0) (𝓝 0)) ∧
    (∀ C : ℝ, ∃ a : ℝ, 0 < a ∧ ∀ t, 0 < t → t ≤ a → epsT C t ≤ 1) ∧
    (∀ (n : ℕ) (a : Fin n → ℝ), (∀ j, 0 < a j) → ∃ b : ℝ, 0 < b ∧ ∀ j, b ≤ a j) :=
  ⟨log_div_self_anti, epsT_mono, le_epsT, epsT_tendsto, epsT_le_one, fin_pos_lower⟩

end GlobalTheory.CompanionTheory.Ar.Num
