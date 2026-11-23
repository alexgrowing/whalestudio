import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem qterm_norm (n : ℕ) (τ : ℍ) :
    ‖cexp (2 * π * Complex.I * n * τ)‖ = Real.exp (-2 * π * τ.im) ^ n := by
  rw [Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem summable_succ_pow_mul_geom (A : ℕ) {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ A * r ^ n := by
  have hs : Summable fun n : ℕ => (n : ℝ) ^ A * r ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one A (by rw [Real.norm_eq_abs, abs_of_pos h0]; exact h1)
  have hs' : Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ A * r ^ (n + 1) :=
    (summable_nat_add_iff 1).2 hs
  have := hs'.mul_left r⁻¹
  refine this.congr fun n => ?_
  push_cast
  rw [pow_succ]
  field_simp

theorem qterm_bound {a : ℕ → ℂ} {C : ℝ} {A : ℕ} (hC : ∀ n : ℕ, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ A)
    {y₀ : ℝ} (n : ℕ) (τ : ℍ) (hτ : y₀ ≤ τ.im) :
    ‖a n * cexp (2 * π * Complex.I * n * τ)‖ ≤ C * ((n : ℝ) + 1) ^ A * Real.exp (-2 * π * y₀) ^ n := by
  rw [norm_mul, qterm_norm]
  have h1 : Real.exp (-2 * π * τ.im) ^ n ≤ Real.exp (-2 * π * y₀) ^ n := by
    apply pow_le_pow_left₀ (Real.exp_pos _).le
    apply Real.exp_le_exp.2
    nlinarith [Real.pi_pos]
  calc ‖a n‖ * Real.exp (-2 * π * τ.im) ^ n ≤ C * ((n : ℝ) + 1) ^ A * Real.exp (-2 * π * τ.im) ^ n :=
        mul_le_mul_of_nonneg_right (hC n) (by positivity)
    _ ≤ C * ((n : ℝ) + 1) ^ A * Real.exp (-2 * π * y₀) ^ n := by
        apply mul_le_mul_of_nonneg_left h1
        exact le_trans (norm_nonneg _) (hC n)

theorem qterm_summable_bound {C : ℝ} (A : ℕ) {y₀ : ℝ} (hy : 0 < y₀) :
    Summable fun n : ℕ => C * ((n : ℝ) + 1) ^ A * Real.exp (-2 * π * y₀) ^ n := by
  have h := summable_succ_pow_mul_geom A (r := Real.exp (-2 * π * y₀)) (Real.exp_pos _)
    (Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos]))
  simpa [mul_assoc] using h.mul_left C

theorem qs_summable_continuous : ∀ a : ℕ → ℂ, PolyB a →
    (∀ τ : ℍ, Summable fun n : ℕ => ‖a n * cexp (2 * π * Complex.I * n * τ)‖) ∧ Continuous (qs a) := by
  intro a ⟨C, A, hC⟩
  refine ⟨fun τ => ?_, ?_⟩
  · exact (qterm_summable_bound (C := C) A τ.im_pos).of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => qterm_bound hC n τ le_rfl)
  · rw [continuous_iff_continuousAt]
    intro τ₀
    have hy : 0 < τ₀.im / 2 := half_pos τ₀.im_pos
    have hopen : IsOpen {τ : ℍ | τ₀.im / 2 < τ.im} :=
      isOpen_lt continuous_const UpperHalfPlane.continuous_im
    have hmem : τ₀ ∈ {τ : ℍ | τ₀.im / 2 < τ.im} := by
      show τ₀.im / 2 < τ₀.im
      linarith [τ₀.im_pos]
    have hon : ContinuousOn (qs a) {τ : ℍ | τ₀.im / 2 < τ.im} := by
      unfold qs
      refine continuousOn_tsum (fun n => ?_) (qterm_summable_bound (C := C) A hy) ?_
      · apply Continuous.continuousOn
        fun_prop
      · intro n τ hτ
        exact qterm_bound hC n τ (le_of_lt hτ)
    exact hon.continuousAt (hopen.mem_nhds hmem)

end GlobalTheory.EisM
