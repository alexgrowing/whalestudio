import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JacobiSymNegEqOfThreeModFour

open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory

theorem kroneckerTwo_neg_eq_jacobiSym_two (q : ℕ) (hq : q % 4 = 3) :
    GlobalTheoryTheory.kron2 (-(q : ℤ)) = jacobiSym 2 q := by
  have hodd : Odd q := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.at_two hodd, ZMod.χ₈_nat_eq_if_mod_eight]
  unfold GlobalTheoryTheory.kron2
  split_ifs <;> omega

theorem kronSym_neg_eq_jacobiSym_and_two :
    (∀ q n : ℕ, q % 4 = 3 → 0 < n → GlobalTheoryTheory.kronSym (-(q : ℤ)) n = jacobiSym (n : ℤ) q) ∧
      ∀ n : ℕ, Odd n → GlobalTheoryTheory.kronSym 2 n = ZMod.χ₈ (n : ZMod 8) := by
  refine ⟨fun q n hq hn => ?_, fun n hn => ?_⟩
  · unfold GlobalTheoryTheory.kronSym
    have hodd : Odd (n / 2 ^ n.factorization 2) := by
      have h := Nat.not_dvd_ordCompl Nat.prime_two hn.ne'
      exact Nat.odd_iff.mpr (by omega)
    have hmul : 2 ^ n.factorization 2 * (n / 2 ^ n.factorization 2) = n :=
      Nat.ordProj_mul_ordCompl_eq_self n 2
    rw [jacobiSym_neg_eq_of_three_mod_four q _ hq hodd, kroneckerTwo_neg_eq_jacobiSym_two q hq,
      ← jacobiSym.pow_left, ← jacobiSym.mul_left]
    congr 1
    rw [mul_comm]
    exact_mod_cast hmul
  · unfold GlobalTheoryTheory.kronSym
    have h0 : n.factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by have := Nat.odd_iff.mp hn; omega)
    rw [h0, pow_zero, pow_zero, Nat.div_one, mul_one, jacobiSym.at_two hn]

end GlobalTheory
