import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLeNormLFunctionOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsNormDerivLFunctionLe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LFunctionConjEqZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ZeroFreePrincipal
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.ZeroGapNearOne

lemma log_pos {x : ℝ} (hx : 1 ≤ x) : 0 < Real.log (3 * x) := Real.log_pos (by linarith)

lemma weaken {x c d : ℝ} (hx : 1 ≤ x) (hc : 0 < c) (hcd : c ≤ d) :
    c / (x ^ 2 * Real.log (3 * x)) ≤ d / Real.log (3 * x) := by
  have hL := log_pos hx
  have h2 : 1 ≤ x ^ 2 := one_le_pow₀ hx
  apply div_le_div₀ (by linarith) hcd hL
  nlinarith

lemma of_region {x c d t r : ℝ} (hx : 1 ≤ x) (hc : 0 < c) (hcd : c ≤ d) (ht : |t| ≤ 1)
    (h : r < 1 - d / Real.log (x * (|t| + 2))) :
    c / (x ^ 2 * Real.log (3 * x)) ≤ 1 - r := by
  have h0 := abs_nonneg t
  have h1 : 0 < Real.log (x * (|t| + 2)) := Real.log_pos (by nlinarith)
  have h2 : Real.log (x * (|t| + 2)) ≤ Real.log (3 * x) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have h3 : d / Real.log (3 * x) ≤ d / Real.log (x * (|t| + 2)) :=
    div_le_div_of_nonneg_left (by linarith) h1 h2
  have := weaken hx hc hcd
  linarith

lemma log_le_sqrt {x : ℝ} (hx : 1 ≤ x) : Real.log (3 * x) ≤ 4 * √x := by
  have hs : 0 < √x := Real.sqrt_pos.2 (by linarith)
  have hsq : √x * √x = x := Real.mul_self_sqrt (by linarith)
  have h1 : Real.log (3 * x) ≤ Real.log ((2 * √x) ^ 2) :=
    Real.log_le_log (by linarith) (by nlinarith)
  rw [Real.log_pow] at h1
  have h2 := Real.log_le_sub_one_of_pos (show 0 < 2 * √x by positivity)
  push_cast at h1
  linarith

lemma real_case {x a C c δ : ℝ} (hx : 1 ≤ x) (hC : 0 < C) (hδ : 0 ≤ δ) (hc : 0 < c)
    (hca : c ≤ a / (4 * C))
    (h : a / x ^ ((3 : ℝ) / 2) ≤ C * Real.log (3 * x) ^ 2 * δ) :
    c / (x ^ 2 * Real.log (3 * x)) ≤ δ := by
  have hL := log_pos hx
  have hs : 0 < √x := Real.sqrt_pos.2 (by linarith)
  have hsq : √x * √x = x := Real.mul_self_sqrt (by linarith)
  have hx0 : 0 < x := by linarith
  have hp : x ^ ((3 : ℝ) / 2) = x * √x := by
    rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hx0,
      Real.rpow_one]
  rw [hp, div_le_iff₀ (by positivity)] at h
  rw [le_div_iff₀ (by positivity)] at hca
  rw [div_le_iff₀ (by positivity)]
  have hl := log_le_sqrt hx
  have h3 : C * Real.log (3 * x) ^ 2 * δ * (x * √x)
      ≤ (C * Real.log (3 * x) * δ * (x * √x)) * (4 * √x) := by
    calc _ = (C * Real.log (3 * x) * δ * (x * √x)) * Real.log (3 * x) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)
  have h4 : (C * Real.log (3 * x) * δ * (x * √x)) * (4 * √x)
      = δ * (x ^ 2 * Real.log (3 * x)) * (4 * C) := by
    calc _ = 4 * C * Real.log (3 * x) * δ * x * (√x * √x) := by ring
      _ = _ := by rw [hsq]; ring
  have h5 : c * (4 * C) ≤ δ * (x ^ 2 * Real.log (3 * x)) * (4 * C) := by linarith
  exact le_of_mul_le_mul_right h5 (by positivity)

theorem exists_gap : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ),
    (χ ≠ 1 ∨ ρ ≠ 1) → LFunction χ ρ = 0 → |ρ.im| ≤ 1 →
      c / ((q : ℝ) ^ 2 * Real.log (3 * q)) ≤ 1 - ρ.re := by
  obtain ⟨a, ha, Ha⟩ := GlobalTheory.LOneLower.exists_le_norm_LFunction_one
  obtain ⟨C, hC, HC⟩ := GlobalTheory.DirichletDeriv.exists_norm_deriv_LFunction_le
  obtain ⟨d, hd, Hd⟩ := GlobalTheory.ZeroFreeComplex.zero_free_region
  obtain ⟨e, he, He⟩ := GlobalTheory.ZeroFreePrincipal.zero_free
  refine ⟨min (min 1 (a / (4 * C))) (min d e), by positivity, ?_⟩
  intro q _ χ ρ hne hz him
  have hc : 0 < min (min 1 (a / (4 * C))) (min d e) := by positivity
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  by_cases h1 : χ = 1
  · subst h1
    have hρ : ρ ≠ 1 := hne.resolve_left (by simp)
    exact of_region hq hc ((min_le_right _ _).trans (min_le_right _ _)) him (He q ρ hρ hz)
  by_cases h2 : χ ^ 2 ≠ 1 ∨ ρ.im ≠ 0
  · exact of_region hq hc ((min_le_right _ _).trans (min_le_left _ _)) him (Hd q χ ρ h1 hz h2)
  push_neg at h2
  obtain ⟨hsq, hreal⟩ := h2
  have hlt : ρ.re < 1 := by
    by_contra h
    exact LFunction_ne_zero_of_one_le_re χ hne (not_lt.1 h) hz
  by_cases h3 : 1 / Real.log (3 * q) ≤ 1 - ρ.re
  · exact (weaken hq hc ((min_le_left _ _).trans (min_le_left _ _))).trans h3
  push_neg at h3
  refine real_case hq hC (by linarith) hc ((min_le_left _ _).trans (min_le_right _ _)) ?_
  refine (Ha q χ h1 hsq).trans ?_
  have hconv : Convex ℝ {z : ℂ | z.im = 0 ∧ ρ.re ≤ z.re ∧ z.re ≤ 1} := by
    intro x hx y hy s t hs ht hst
    obtain ⟨hx1, hx2, hx3⟩ := hx
    obtain ⟨hy1, hy2, hy3⟩ := hy
    refine ⟨by simp [hx1, hy1], ?_, ?_⟩
    · simp only [add_re, smul_re, smul_eq_mul]
      have : ρ.re = s * ρ.re + t * ρ.re := by rw [← add_mul, hst, one_mul]
      nlinarith [mul_le_mul_of_nonneg_left hx2 hs, mul_le_mul_of_nonneg_left hy2 ht]
    · simp only [add_re, smul_re, smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left hx3 hs, mul_le_mul_of_nonneg_left hy3 ht]
  have key := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ) (f := LFunction χ)
    (C := C * Real.log (3 * q) ^ 2) (x := ρ) (y := 1)
    (fun z _ => differentiable_LFunction h1 z)
    (fun z hz' => by
      obtain ⟨h4, h5, h6⟩ := hz'
      have : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [h4])
      rw [this]
      exact HC q χ h1 z.re (by linarith) h6)
    hconv ⟨hreal, le_rfl, hlt.le⟩ ⟨by simp, by simpa using hlt.le, by simp⟩
  rw [hz, sub_zero] at key
  have hn : ‖(1 : ℂ) - ρ‖ = 1 - ρ.re := by
    have : (1 : ℂ) - ρ = ((1 - ρ.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hreal])
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  rwa [hn] at key

end GlobalTheory.ZeroGapNearOne
