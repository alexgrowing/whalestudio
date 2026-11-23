import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthGamma
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DigammaBoundVerticalStrip

open Complex Set
open scoped Real

namespace GlobalTheory.CompanionTheory.InvGammaStrip

theorem norm_inv_Gamma_le_reflect {z : ℂ} (hre : z.re < 1) (him : z.im ≠ 0) :
    ‖(Complex.Gamma z)⁻¹‖ ≤ Real.Gamma (1 - z.re) * Real.exp (π * |z.im|) / π := by
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsin : Complex.sin (π * z) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k hk
    have h := congrArg Complex.im hk
    simp [Real.pi_ne_zero] at h
    exact him h
  have hG : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero fun m h => him (by rw [h]; simp)
  have hinv : (Complex.Gamma z)⁻¹ = Complex.Gamma (1 - z) * Complex.sin (π * z) / π := by
    have h6 : Complex.Gamma z * Complex.Gamma (1 - z) * Complex.sin (π * z) = π := by
      rw [Complex.Gamma_mul_Gamma_one_sub, div_mul_cancel₀ _ hsin]
    refine eq_div_of_mul_eq hpi ?_
    rw [inv_mul_eq_iff_eq_mul₀ hG]
    linear_combination -h6
  have h1 : ‖Complex.Gamma (1 - z)‖ ≤ Real.Gamma (1 - z.re) := by
    have := PI.EF.norm_Gamma_le (w := 1 - z) (by simp; linarith)
    simpa using this
  have h2 : ‖Complex.sin (π * z)‖ ≤ Real.exp (π * |z.im|) := by
    refine (GlobalTheory.CompanionTheory.DigammaStrip.norm_sin_le_exp _).trans (le_of_eq ?_)
    congr 1
    simp [abs_mul, abs_of_pos Real.pi_pos]
  rw [hinv, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  gcongr

theorem exists_bound_left (a : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ 1 / 2 → z.im ≠ 0 →
      ‖(Complex.Gamma z)⁻¹‖ ≤ K * Real.exp (π * |z.im|) := by
  have hc : ContinuousOn Real.Gamma (Icc (1 / 2) (max (1 / 2) (1 - a))) := fun x hx =>
    (Real.differentiableAt_Gamma fun m h => by
      have h0 := hx.1
      have h1 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      rw [h] at h0
      linarith).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨|M| / π, by positivity, fun z h1 h2 h3 => ?_⟩
  refine (norm_inv_Gamma_le_reflect (by linarith) h3).trans ?_
  have hb : Real.Gamma (1 - z.re) ≤ |M| := by
    have := hM (1 - z.re) ⟨by linarith, le_max_of_le_right (by linarith)⟩
    exact (le_abs_self _).trans (this.trans (le_abs_self _))
  rw [div_mul_eq_mul_div]
  gcongr

theorem exists_bound_far (a b : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → 1 ≤ |z.im| →
      ‖(Complex.Gamma z)⁻¹‖ ≤ K * Real.exp (π * |z.im|) := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_left (min a (-1 / 2))
  refine ⟨K, hK0, ?_⟩
  have key : ∀ n : ℕ, ∀ z : ℂ, min a (-1 / 2) ≤ z.re → z.re ≤ 1 / 2 + n → 1 ≤ |z.im| →
      ‖(Complex.Gamma z)⁻¹‖ ≤ K * Real.exp (π * |z.im|) := by
    intro n
    induction n with
    | zero =>
      intro z h1 h2 h3
      refine hK z h1 (by simpa using h2) ?_
      intro h
      rw [h, abs_zero] at h3
      linarith
    | succ n ih =>
      intro z h1 h2 h3
      by_cases hz : z.re ≤ 1 / 2 + n
      · exact ih z h1 hz h3
      push_neg at hz
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hlow : min a (-1 / 2) ≤ (z - 1).re := by
        have : min a (-1 / 2) ≤ -1 / 2 := min_le_right _ _
        simp only [sub_re, one_re]
        linarith
      have hup : (z - 1).re ≤ 1 / 2 + n := by
        push_cast at h2
        simp only [sub_re, one_re]
        linarith
      have him : (z - 1).im = z.im := by simp
      have h := ih (z - 1) hlow hup (by rwa [him])
      rw [him] at h
      have hrec := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (z - 1)
      rw [sub_add_cancel] at hrec
      have hnorm : 1 ≤ ‖z - 1‖ := h3.trans (by
        rw [← him]
        exact Complex.abs_im_le_norm _)
      have hle : ‖(Complex.Gamma z)⁻¹‖ ≤ ‖(Complex.Gamma (z - 1))⁻¹‖ := by
        rw [hrec, norm_mul]
        exact le_mul_of_one_le_left (norm_nonneg _) hnorm
      exact hle.trans h
  intro z h1 h2 h3
  obtain ⟨n, hn⟩ := exists_nat_ge b
  exact key n z ((min_le_left _ _).trans h1) (by linarith) h3

theorem exists_norm_inv_Gamma_le (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖(Complex.Gamma z)⁻¹‖ ≤ C * Real.exp (π * |z.im|) := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_far a b
  have hcomp : IsCompact (Icc a b ×ℂ Icc (-1 : ℝ) 1) := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨D, hD⟩ := hcomp.exists_bound_of_continuousOn
    Complex.differentiable_one_div_Gamma.continuous.continuousOn
  refine ⟨max K |D|, le_max_of_le_left hK0, fun z h1 h2 => ?_⟩
  have hexp : 1 ≤ Real.exp (π * |z.im|) := Real.one_le_exp (by positivity)
  by_cases hz : 1 ≤ |z.im|
  · exact (hK z h1 h2 hz).trans (by gcongr; exact le_max_left _ _)
  · push_neg at hz
    have hmem : z ∈ Icc a b ×ℂ Icc (-1 : ℝ) 1 :=
      Complex.mem_reProdIm.2 ⟨⟨h1, h2⟩, (abs_le.1 hz.le)⟩
    have h := hD z hmem
    calc ‖(Complex.Gamma z)⁻¹‖ ≤ |D| := h.trans (le_abs_self _)
      _ ≤ max K |D| := le_max_right _ _
      _ ≤ max K |D| * Real.exp (π * |z.im|) :=
        le_mul_of_one_le_right (le_max_of_le_left hK0) hexp

end GlobalTheory.CompanionTheory.InvGammaStrip
