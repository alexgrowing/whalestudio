import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.SamePrimesMulPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.StickelbergerCarrySpecAndWeightOneCoeffOfOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.StickelbergerBernoulliCoeffExpansionModDenominat
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.ExistsBinomialExpansionModSq

open Finset UpperTheory.V.Bern UpperTheory.V.Stk

theorem UpperTheory.V.Stk.twistedBernoulliValue_congr_pow_mul_first :
    ∀ (M a e : ℕ) [NeZero M], a.Coprime M → Odd a → ∀ b : ZMod M, ∃ z : ℤ,
      Eva M (e + 1) a b = (((b.val : ℤ) ^ e * Eone M a b : ℤ) : ℚ) + (M : ℚ) / (dk (e + 1) : ℚ) * z := by
  intro M a e _ ha ho b
  have hM0 : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hM : (M : ℚ) ≠ 0 := by exact_mod_cast hM0.ne'
  have hD : (primorial (e + 1 + 1) : ℚ) ≠ 0 := by exact_mod_cast (primorial_pos _).ne'
  have hk : (e : ℚ) + 1 ≠ 0 := by positivity
  have h1 := (stickelbergerCarry_spec_and_weightOne_coeff_of_odd M a ha b).1
  obtain ⟨z1, hz1⟩ := stickelbergerBernoulliCoeff_expansion_mod_denominator M e b.val hM0
  obtain ⟨z2, hz2⟩ := stickelbergerBernoulliCoeff_expansion_mod_denominator M e (yCl a b).val hM0
  obtain ⟨⟨z3, hz3⟩, ⟨w, hw⟩⟩ := exists_binomial_expansion_mod_sq (b.val : ℤ) (jv M a b) M e
  rw [← h1, mul_pow] at hz3 hw
  obtain ⟨c, hc⟩ := ho
  have h2 : ((a : ℤ) - 1) / 2 = c := by omega
  have h4 : (a : ℚ) = 2 * c + 1 := by exact_mod_cast hc
  have h6 : (c : ℚ) = ((a : ℚ) - 1) / 2 := by rw [h4]; ring
  have q3 : (a : ℚ) ^ (e + 1) * ((yCl a b).val : ℚ) ^ (e + 1) =
      (b.val : ℚ) ^ (e + 1) + ((e : ℚ) + 1) * (b.val : ℚ) ^ e * ((M : ℚ) * (jv M a b : ℚ)) + (M : ℚ) ^ 2 * z3 := by
    exact_mod_cast hz3
  have qw : (a : ℚ) ^ e * ((yCl a b).val : ℚ) ^ e = (b.val : ℚ) ^ e + (M : ℚ) * w := by
    exact_mod_cast hw
  have hdk : (dk (e + 1) : ℚ) = 2 * ((e : ℚ) + 1) * (primorial (e + 1 + 1) : ℚ) := by
    rw [dk]; push_cast; ring
  refine ⟨2 * z1 - 2 * (a : ℤ) ^ (e + 1) * z2 - 2 * (primorial (e + 1 + 1) : ℤ) * z3
    + ((e : ℤ) + 1) * (primorial (e + 1 + 1) : ℤ) * a * w, ?_⟩
  rw [Eva, Ev, Ev, hz1, hz2, Eone, h2, hdk]
  push_cast
  rw [h6]
  have e1 : ∀ R : ℚ, (a : ℚ) ^ (e + 1) * (((yCl a b).val : ℚ) ^ (e + 1) / (((e : ℚ) + 1) * M) -
      ((yCl a b).val : ℚ) ^ e / 2 + R) =
      ((a : ℚ) ^ (e + 1) * ((yCl a b).val : ℚ) ^ (e + 1)) / (((e : ℚ) + 1) * M) -
        a * ((a : ℚ) ^ e * ((yCl a b).val : ℚ) ^ e) / 2 + (a : ℚ) ^ (e + 1) * R := by
    intro R; ring
  rw [e1, q3, qw]
  field_simp
  ring
