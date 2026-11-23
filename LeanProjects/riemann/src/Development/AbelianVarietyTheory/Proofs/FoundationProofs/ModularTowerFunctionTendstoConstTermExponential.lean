import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Definitions.Foundations.SiegelNeZeroIff
open scoped MatrixGroups
open GlobalTheory.KZ

namespace GlobalTheory.KZ.ExpBound

theorem series_bound (a : ℕ → ℂ) (ψ : ℂ → ℂ) (C : ℝ)
    (hs : ∀ z : ℂ, C < z.im →
      HasSum (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z)) (ψ z)) :
    ∃ B t : ℝ, ∀ w : ℂ, t < w.im → ‖ψ w - a 0‖ ≤ B * Real.exp (-(2 * Real.pi * (w.im - t))) := by
  have hnorm : ∀ (n : ℕ) (z : ℂ), ‖a n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z)‖ =
      ‖a n‖ * Real.exp (-(2 * Real.pi * n * z.im)) := by
    intro n z
    rw [norm_mul, Complex.norm_exp]
    congr 2
    simp [Complex.mul_re, Complex.mul_im]
  set t0 : ℝ := C + 1 with ht0
  have hz0 : ((t0 : ℂ) * Complex.I).im = t0 := by simp
  have hsm : Summable (fun n : ℕ => ‖a n‖ * Real.exp (-(2 * Real.pi * n * t0))) := by
    have h1 := (hs ((t0 : ℂ) * Complex.I) (by rw [hz0]; linarith)).summable
    have h2 := summable_norm_iff.mpr h1
    simpa only [hnorm, hz0] using h2
  set B0 : ℝ := ∑' n : ℕ, ‖a n‖ * Real.exp (-(2 * Real.pi * n * t0)) with hB0
  have hle : ∀ n : ℕ, ‖a n‖ * Real.exp (-(2 * Real.pi * n * t0)) ≤ B0 := fun n =>
    hsm.le_tsum n (fun j _ => by positivity)
  have hB0nn : 0 ≤ B0 := tsum_nonneg (fun j => by positivity)
  refine ⟨2 * B0, t0 + 1, fun w hw => ?_⟩
  set ρ : ℝ := Real.exp (-(2 * Real.pi * (w.im - t0))) with hρ
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hpi := Real.pi_gt_three
  have hρ2 : ρ ≤ 1 / 2 := by
    have h1 : 1 ≤ 2 * Real.pi * (w.im - t0) := by nlinarith
    have h2 := Real.add_one_le_exp (2 * Real.pi * (w.im - t0))
    rw [hρ, Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) (by linarith)
  have hsh := (hasSum_nat_add_iff' 1).mpr (hs w (by linarith))
  simp only [Finset.sum_range_one, Nat.cast_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one] at hsh
  have hg : HasSum (fun n : ℕ => B0 * ρ * ρ ^ n) (B0 * ρ * (1 - ρ)⁻¹) :=
    (hasSum_geometric_of_lt_one hρ0.le (by linarith)).mul_left _
  have hb := tsum_of_norm_bounded hg (f := fun n : ℕ =>
      a (n + 1) * Complex.exp (2 * Real.pi * Complex.I * ((n + 1 : ℕ) : ℂ) * w)) (fun n => by
    rw [hnorm]
    have e : Real.exp (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * w.im)) =
        Real.exp (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t0)) * ρ ^ (n + 1) := by
      rw [hρ, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    rw [e, ← mul_assoc, mul_assoc B0, ← pow_succ']
    exact mul_le_mul_of_nonneg_right (hle (n + 1)) (by positivity))
  rw [hsh.tsum_eq] at hb
  have h3 : B0 * ρ * (1 - ρ)⁻¹ ≤ 2 * B0 * ρ := by
    rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg (mul_nonneg hB0nn hρ0.le) (show 0 ≤ 1 - 2 * ρ by linarith)]
  have h4 : ρ ≤ Real.exp (-(2 * Real.pi * (w.im - (t0 + 1)))) := by
    rw [hρ]
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc ‖ψ w - a 0‖ ≤ B0 * ρ * (1 - ρ)⁻¹ := hb
    _ ≤ 2 * B0 * ρ := h3
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)

theorem bound_at_infinity : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (h : X.K) (φ : ℂ → ℂ), ContinuousOn φ Hs → X.an h = (φ : Mero) → (∀ r : ℚ, (X.exp h).coeff r ≠ 0 → ∃ n : ℕ, r = n) → ∃ B t : ℝ, ∀ z ∈ Hs, t < z.im → ‖φ z - ε ((X.exp h).coeff 0)‖ ≤ B * Real.exp (-(2 * Real.pi * (z.im - t))) := by
  intro Ω _ _ ε X h φ hφc hφ hsupp
  obtain ⟨φ', C, hφ', hsum⟩ := X.an_exp h
  have hsumN : ∀ z : ℂ, C < z.im → HasSum (fun n : ℕ => ε ((X.exp h).coeff (n : ℚ)) *
      Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z)) (φ' z) := by
    intro z hz
    have h1 := hsum z hz
    rw [← (Nat.cast_injective (R := ℚ)).hasSum_iff] at h1
    · simpa [Function.comp_def] using h1
    · intro r hr
      have : (X.exp h).coeff r = 0 := by
        by_contra hne
        obtain ⟨n, rfl⟩ := hsupp r hne
        exact hr ⟨n, rfl⟩
      simp [this]
  obtain ⟨B, t, hB⟩ := series_bound (fun n : ℕ => ε ((X.exp h).coeff (n : ℚ))) φ' C hsumN
  simp only [Nat.cast_zero] at hB
  refine ⟨B, t, fun z hz htz => ?_⟩
  have hev : φ =ᶠ[Filter.codiscreteWithin Hs] φ' := Filter.Germ.coe_eq.mp (hφ.symm.trans hφ')
  have h1 := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hev z hz
  have hHs : Hs ∈ nhds z := SiegelModel.isOpen_Hs.mem_nhds hz
  have h2 : Hs ∈ nhdsWithin z {z}ᶜ := mem_nhdsWithin_of_mem_nhds hHs
  have h3 : {w : ℂ | t < w.im} ∈ nhdsWithin z {z}ᶜ :=
    mem_nhdsWithin_of_mem_nhds ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds htz)
  have hl : Filter.Tendsto (fun w => ‖φ w - ε ((X.exp h).coeff 0)‖) (nhdsWithin z {z}ᶜ)
      (nhds ‖φ z - ε ((X.exp h).coeff 0)‖) :=
    (((hφc.continuousAt hHs).sub continuousAt_const).norm.tendsto).mono_left nhdsWithin_le_nhds
  have hc : Continuous fun w : ℂ => B * Real.exp (-(2 * Real.pi * (w.im - t))) := by fun_prop
  refine le_of_tendsto_of_tendsto hl ((hc.tendsto z).mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [h1, h2, h3] with w hw1 hw2 hw3
  rcases hw1 with e | e
  · have e' : φ w = φ' w := e
    rw [e']
    exact hB w hw3
  · exact absurd hw2 e

end GlobalTheory.KZ.ExpBound
