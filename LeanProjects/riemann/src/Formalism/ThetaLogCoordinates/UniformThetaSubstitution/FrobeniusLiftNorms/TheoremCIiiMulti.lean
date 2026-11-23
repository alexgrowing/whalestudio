import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.HeckeOneLift
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.GaussElementarySymmetric

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open CSym

namespace C2

lemma scal {K : Type} [Field K] (Q N g i l : ℕ) (hQ : (Q : K) ≠ 0) (hl : l ≤ i) (a b : K)
    (hb : b ≠ 0) :
    (Q : K) ^ (-((i : ℤ) * ((N : ℤ) + g - i))) *
        (a ^ i * (Q : K) ^ (i * N) *
          (((Q ^ 2) ^ ((i - l) * (g - l)) * Formalism.G0.gaussBinom (Q ^ 2) g l : ℕ) : K) *
          (b ^ (i - l) * (Q : K) ^ ((i - l) * (N + g)))⁻¹) =
      (a / b) ^ i * eF (fun x => b * beFam (Q : K) g x) l *
        (Q : K) ^ (-(((i - l : ℕ) : ℤ) * ((N : ℤ) - (i - l : ℕ)))) := by
  push_cast
  rw [gauss_zpow Q hQ g l, eF_smul]
  rcases le_or_gt l g with h | h
  · generalize eF (beFam (Q : K) g) l = E
    have key : (Q : K) ^ (-((i : ℤ) * ((N : ℤ) + g - i))) * (Q : K) ^ (i * N) *
        (((Q : K) ^ 2) ^ ((i - l) * (g - l)) * (Q : K) ^ ((l : ℤ) * ((g : ℤ) - l))) =
        (Q : K) ^ (-(((i - l : ℕ) : ℤ) * ((N : ℤ) - (i - l : ℕ)))) *
          (Q : K) ^ ((i - l) * (N + g)) := by
      rw [← pow_mul, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hQ,
        ← zpow_add₀ hQ, ← zpow_add₀ hQ, ← zpow_add₀ hQ]
      congr 1
      push_cast [Nat.cast_sub h, Nat.cast_sub hl]
      ring
    have hX : (Q : K) ^ ((i - l) * (N + g)) * ((Q : K) ^ ((i - l) * (N + g)))⁻¹ = 1 :=
      mul_inv_cancel₀ (pow_ne_zero _ hQ)
    have hB : (a / b) ^ i * b ^ l = a ^ i * (b ^ (i - l))⁻¹ := by
      have e : b ^ i = b ^ (i - l) * b ^ l := by rw [← pow_add]; congr 1; omega
      rw [div_pow, e]
      field_simp
    rw [mul_inv]
    linear_combination (a ^ i * E * (b ^ (i - l))⁻¹ * ((Q : K) ^ ((i - l) * (N + g)))⁻¹) * key +
      (a ^ i * E * (b ^ (i - l))⁻¹ *
        (Q : K) ^ (-(((i - l : ℕ) : ℤ) * ((N : ℤ) - (i - l : ℕ))))) * hX -
      (E * (Q : K) ^ (-(((i - l : ℕ) : ℤ) * ((N : ℤ) - (i - l : ℕ))))) * hB
  · rw [eF_of_card_lt _ _ (by simpa using h)]
    simp

end C2

end Formalism.InvariantFactorPaths.G7
