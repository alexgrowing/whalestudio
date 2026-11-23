import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.DzDifferentiableOn
import Formalism.SizeWindowBrackets.SlopesFromSizeAndCount

open Complex Filter Topology

noncomputable section

namespace Formalism.LFunctionChainParameters.LChain6.Chi8

open Formalism.ZF.ComplexPowerDifferenceIntegral

def chi : DirichletCharacter ℂ 8 := ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)

def g (s : ℂ) (n : ℕ) : ℂ :=
  ((8 * (n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - ((8 * (n : ℝ) + 3 : ℝ) : ℂ) ^ (-s)
    - (((8 * (n : ℝ) + 5 : ℝ) : ℂ) ^ (-s) - ((8 * (n : ℝ) + 7 : ℝ) : ℂ) ^ (-s))

def G (s : ℂ) : ℂ := ∑' n, g s n

lemma chi_apply (x : ZMod 8) : chi x = ((ZMod.χ₈ x : ℤ) : ℂ) := rfl

lemma chi_cast (m r : ℕ) : chi ((m * 8 + r : ℕ) : ZMod 8) = chi ((r : ℕ) : ZMod 8) := by
  have h8 : ((8 : ℕ) : ZMod 8) = 0 := ZMod.natCast_self 8
  rw [Nat.cast_add, Nat.cast_mul, h8, mul_zero, zero_add]

lemma chi0 : chi ((0 : ℕ) : ZMod 8) = 0 := by
  rw [chi_apply, show ZMod.χ₈ ((0 : ℕ) : ZMod 8) = 0 by decide]; simp
lemma chi1 : chi ((1 : ℕ) : ZMod 8) = 1 := by
  rw [chi_apply, show ZMod.χ₈ ((1 : ℕ) : ZMod 8) = 1 by decide]; simp
lemma chi2 : chi ((2 : ℕ) : ZMod 8) = 0 := by
  rw [chi_apply, show ZMod.χ₈ ((2 : ℕ) : ZMod 8) = 0 by decide]; simp
lemma chi3 : chi ((3 : ℕ) : ZMod 8) = -1 := by
  rw [chi_apply, show ZMod.χ₈ ((3 : ℕ) : ZMod 8) = -1 by decide]; simp
lemma chi4 : chi ((4 : ℕ) : ZMod 8) = 0 := by
  rw [chi_apply, show ZMod.χ₈ ((4 : ℕ) : ZMod 8) = 0 by decide]; simp
lemma chi5 : chi ((5 : ℕ) : ZMod 8) = -1 := by
  rw [chi_apply, show ZMod.χ₈ ((5 : ℕ) : ZMod 8) = -1 by decide]; simp
lemma chi6 : chi ((6 : ℕ) : ZMod 8) = 0 := by
  rw [chi_apply, show ZMod.χ₈ ((6 : ℕ) : ZMod 8) = 0 by decide]; simp
lemma chi7 : chi ((7 : ℕ) : ZMod 8) = 1 := by
  rw [chi_apply, show ZMod.χ₈ ((7 : ℕ) : ZMod 8) = 1 by decide]; simp

def tm (s : ℂ) (n : ℕ) : ℂ := LSeries.term (fun n : ℕ => chi (n : ZMod 8)) s n

lemma tm_zero (s : ℂ) (m r : ℕ) (h : chi ((r : ℕ) : ZMod 8) = 0) : tm s (m * 8 + r) = 0 := by
  unfold tm
  rw [LSeries.term_def]
  split_ifs
  · rfl
  · rw [chi_cast, h, zero_div]

lemma tm_eval (s : ℂ) (m r : ℕ) (hr : 0 < r) :
    tm s (m * 8 + r) = chi ((r : ℕ) : ZMod 8) * ((8 * (m : ℝ) + (r : ℝ) : ℝ) : ℂ) ^ (-s) := by
  unfold tm
  rw [LSeries.term_of_ne_zero (by omega), chi_cast, Complex.cpow_neg, div_eq_mul_inv]
  congr 3
  push_cast
  ring

lemma block (s : ℂ) (m : ℕ) : ∑ r : Fin 8, tm s (m * 8 + (r : ℕ)) = g s m := by
  rw [Fin.sum_univ_eight]
  change tm s (m * 8 + 0) + tm s (m * 8 + 1) + tm s (m * 8 + 2) + tm s (m * 8 + 3) + tm s (m * 8 + 4)
    + tm s (m * 8 + 5) + tm s (m * 8 + 6) + tm s (m * 8 + 7) = g s m
  rw [tm_zero s m 0 chi0, tm_zero s m 2 chi2, tm_zero s m 4 chi4, tm_zero s m 6 chi6,
    tm_eval s m 1 (by norm_num), tm_eval s m 3 (by norm_num), tm_eval s m 5 (by norm_num),
    tm_eval s m 7 (by norm_num), chi1, chi3, chi5, chi7]
  unfold g
  simp only [Nat.cast_ofNat, Nat.cast_one]
  ring

def gr (σ : ℝ) (n : ℕ) : ℝ :=
  (8 * (n : ℝ) + 1) ^ (-σ) - (8 * (n : ℝ) + 3) ^ (-σ) - ((8 * (n : ℝ) + 5) ^ (-σ) - (8 * (n : ℝ) + 7) ^ (-σ))

end Formalism.LFunctionChainParameters.LChain6.Chi8

namespace Formalism.LFunctionChainParameters.LChain6

end Formalism.LFunctionChainParameters.LChain6
