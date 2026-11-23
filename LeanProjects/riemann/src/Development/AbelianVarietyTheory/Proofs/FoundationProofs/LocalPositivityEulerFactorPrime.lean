import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RootsNormLeOfBoundedTwoStepRecurrence
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpNormProductLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoStepRecursionLocalEulerFactorsStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.LocIneq

theorem term_prime_pow (b : ℕ → ℂ) (s : ℝ) (p : ℕ) (hp : p.Prime) (e : ℕ) :
    LSeries.term b ((1 + s : ℝ) : ℂ) (p ^ e) = b (p ^ e) * ((1 / (p : ℝ) ^ (1 + s) : ℝ) : ℂ) ^ e := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hne : p ^ e ≠ 0 := pow_ne_zero _ hp.ne_zero
  rw [LSeries.term_of_ne_zero hne]
  have h1 : ((p ^ e : ℕ) : ℂ) ^ ((1 + s : ℝ) : ℂ) = ((((p : ℝ) ^ (1 + s)) ^ e : ℝ) : ℂ) := by
    rw [show ((p ^ e : ℕ) : ℂ) = (((p ^ e : ℕ) : ℝ) : ℂ) by push_cast; rfl]
    rw [← Complex.ofReal_cpow (Nat.cast_nonneg _)]
    congr 1
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul hp0, mul_comm, Real.rpow_mul_natCast hp0]
  rw [h1, div_eq_mul_inv]
  congr 1
  push_cast
  rw [one_div, inv_pow]

theorem real_term_prime_pow (b : ℕ → ℂ) (s : ℝ) (p : ℕ) (e : ℕ) :
    ‖b (p ^ e)‖ ^ 2 / ((p ^ e : ℕ) : ℝ) ^ (1 + s) = ‖b (p ^ e)‖ ^ 2 * (1 / (p : ℝ) ^ (1 + s)) ^ e := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  rw [Nat.cast_pow, ← Real.rpow_natCast_mul hp0, mul_comm, Real.rpow_mul_natCast hp0, div_eq_mul_inv,
    one_div, inv_pow]

theorem local_positivity_eulerFactor : ∀ (b ω : ℕ → ℂ) (s C : ℝ) (p : ℕ), 0 < s → p.Prime → b 1 = 1 → ‖ω p‖ = 1 → (∀ r : ℕ, b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - ω p * b (p ^ r)) → (∀ n : ℕ, ‖b n‖ ^ 2 ≤ C * n) → Real.exp (‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s)) ≤ (1 - 1 / (p : ℝ) ^ (1 + s))⁻¹ * ‖∑' e : ℕ, LSeries.term b ((1 + s : ℝ) : ℂ) (p ^ e)‖ ^ 2 * (∑' e : ℕ, ‖b (p ^ e)‖ ^ 2 / ((p ^ e : ℕ) : ℝ) ^ (1 + s)) * (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹ := by
  intro b ω s C p hs hp hb1 hω hrec hbd
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hC : 0 ≤ C := by
    have := hbd 1
    rw [hb1] at this
    simp at this
    linarith
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_eq_mul_self (b p ^ 2 - 4 * ω p)
  set x : ℂ := (b p + z) / 2 with hx
  set y : ℂ := (b p - z) / 2 with hy
  have hxy : x + y = b p := by rw [hx, hy]; ring
  have hxy' : x * y = ω p := by rw [hx, hy]; linear_combination (1 / 4 : ℂ) * hz
  have hc0 : b (p ^ 0) = 1 := by simpa using hb1
  have hc1 : b (p ^ 1) = x + y := by rw [pow_one, hxy]
  have hcr : ∀ r, b (p ^ (r + 2)) = (x + y) * b (p ^ (r + 1)) - x * y * b (p ^ r) := by
    intro r; rw [hxy, hxy']; exact hrec r
  have hroots := GlobalTheory.roots_norm_le_of_bounded_two_step_recursion x y (fun r => b (p ^ r))
    (Real.sqrt C) (Real.sqrt p) (Real.sqrt_nonneg _) hc0 hc1 hcr (by
      intro r
      have h := hbd (p ^ r)
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
      rw [mul_pow, ← pow_mul, mul_comm r 2, pow_mul, Real.sq_sqrt hC, Real.sq_sqrt hp0.le]
      simpa using h)
  have hP : (p : ℝ) < (p : ℝ) ^ (1 + s) := by
    conv_lhs => rw [← Real.rpow_one (p : ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt hp1 (by linarith)
  have hP0 : 0 < (p : ℝ) ^ (1 + s) := by linarith
  have hsq : 1 / (p : ℝ) ^ (2 * (1 + s)) = (1 / (p : ℝ) ^ (1 + s)) ^ 2 := by
    rw [mul_comm, Real.rpow_mul hp0.le, Real.rpow_two, div_pow, one_pow]
  simp only [term_prime_pow b s p hp, real_term_prime_pow b s p, hsq]
  rw [div_eq_mul_one_div (‖1 + b p‖ ^ 2)]
  have hT0 : 0 < 1 / (p : ℝ) ^ (1 + s) := by positivity
  have hpT : p * (1 / (p : ℝ) ^ (1 + s)) < 1 := by
    rw [mul_one_div, div_lt_one hP0]; exact hP
  generalize 1 / (p : ℝ) ^ (1 + s) = T at hT0 hpT ⊢
  have hT1 : T < 1 := by nlinarith
  have hb : ∀ w : ℂ, ‖w‖ ≤ Real.sqrt p → ‖w‖ ^ 2 * T < 1 := by
    intro w hw
    have : ‖w‖ ^ 2 ≤ p := by
      rw [← Real.sq_sqrt hp0.le]
      exact pow_le_pow_left₀ (norm_nonneg _) hw 2
    nlinarith
  have hxT := hb x hroots.1
  have hyT := hb y hroots.2
  obtain ⟨hL, hR⟩ := GlobalTheory.T.twoStepRecursion_localEulerFactors x y (fun r => b (p ^ r)) T hT0.le hT1 hxT hyT hc0 hc1 hcr
  have hI := GlobalTheory.EisM.locineq x y T hT0.le hT1 hxT hyT
  rw [add_assoc, hxy] at hI
  rw [hxy', hω] at hR
  have hR0 : 0 ≤ ∑' r : ℕ, ‖b (p ^ r)‖ ^ 2 * T ^ r := tsum_nonneg fun r => by positivity
  have hLn := congrArg (fun w : ℂ => ‖w‖ ^ 2) hL
  simp only [norm_one, one_pow] at hLn
  rw [norm_mul, mul_pow] at hLn
  have hL0 : 0 ≤ ‖∑' r : ℕ, b (p ^ r) * (T : ℂ) ^ r‖ ^ 2 := by positivity
  generalize (∑' r : ℕ, ‖b (p ^ r)‖ ^ 2 * T ^ r) = R at hR hR0 ⊢
  generalize ‖∑' r : ℕ, b (p ^ r) * (T : ℂ) ^ r‖ ^ 2 = L at hLn hL0 ⊢
  generalize ‖(1 - x * T) * (1 - y * T)‖ ^ 2 = D at hLn hI
  generalize (1 - ‖x‖ ^ 2 * T) * (1 - ‖y‖ ^ 2 * T) * ‖1 - x * conj y * T‖ ^ 2 = E at hR hI
  generalize Real.exp (‖1 + b p‖ ^ 2 * T) = A at hI ⊢
  have h1 : 0 < 1 - T := by linarith
  have h2 : 0 < 1 - T ^ 2 := by nlinarith
  rw [one_pow, one_mul] at hR
  have hK : 0 ≤ (1 - T)⁻¹ * L * R * (1 - T ^ 2)⁻¹ := by positivity
  have hone : ((1 - T) * D * E) * ((1 - T)⁻¹ * L * R * (1 - T ^ 2)⁻¹) = 1 := by
    calc ((1 - T) * D * E) * ((1 - T)⁻¹ * L * R * (1 - T ^ 2)⁻¹)
        = ((1 - T) * (1 - T)⁻¹) * (L * D) * ((R * E) * (1 - T ^ 2)⁻¹) := by ring
      _ = 1 := by rw [hLn, hR, mul_inv_cancel₀ h1.ne', mul_inv_cancel₀ h2.ne']; ring
  have h3 := mul_le_mul_of_nonneg_right hI hK
  rwa [mul_assoc, hone, mul_one, one_mul] at h3

end GlobalTheory.LocIneq
