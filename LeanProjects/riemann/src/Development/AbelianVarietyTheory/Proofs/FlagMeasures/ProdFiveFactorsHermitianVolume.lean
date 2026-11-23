import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqSumEqSumSqAddTwoMulSumLt

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FiveFactors

theorem volU_eq (k : ℕ) : GlobalTheory.FlagMeas.volU k = sphV k * (2 : ℝ) ^ (((k : ℝ) ^ 2 - k) / 2) := by
  unfold GlobalTheory.FlagMeas.volU
  congr 1
  rw [← Real.rpow_natCast, ← Nat.choose_two_right, Nat.cast_choose_two]
  congr 1
  ring

theorem sum_Ioc_half (m n : ℕ) (h : m ≤ n) :
    ∑ M ∈ Finset.Ioc m n, ((M : ℝ) - 1 / 2) = ((n : ℝ) ^ 2 - (m : ℝ) ^ 2) / 2 := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n h ih =>
    rw [Finset.sum_Ioc_succ_top h, ih]
    push_cast
    ring

theorem vInv_pos (E : Type) [Field E] [NumberField E] : 0 < Formalism.HermitianLatticesTheory.vInv E := by
  unfold Formalism.HermitianLatticesTheory.vInv
  have : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero E)
  positivity

theorem prod_rankFac (E : Type) [Field E] [NumberField E] [StarRing E] (m n : ℕ) (h : m ≤ n) :
    ∏ M ∈ Finset.Ioc m n, rankFac E M =
      (2 * Formalism.HermitianLatticesTheory.vInv E) ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) * (((n : ℝ) ^ 2 - (m : ℝ) ^ 2) / 2)) *
        ∏ M ∈ Finset.Ioc m n, Formalism.HermitianLatticesTheory.lValEta E M := by
  have hv := vInv_pos E
  unfold rankFac
  rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos (by positivity), ← Finset.mul_sum,
    sum_Ioc_half m n h]

theorem dimN_eq (n a : ℕ) (j : Fin a → ℕ) (h : 2 * ∑ i, j i ≤ n) :
    (dimN n j : ℝ) = 2 * ((∑ i, j i : ℕ) : ℝ) ^ 2 - ∑ i, (j i : ℝ) ^ 2
      + 2 * ((∑ i, j i : ℕ) : ℝ) * (n - 2 * ((∑ i, j i : ℕ) : ℝ)) := by
  have h1 := (GlobalTheory.dim_unipotent_radical_identities a (fun i => (j i : ℤ)) n).1
  have h2 : (dimN n j : ℤ) = 2 * ((∑ i, j i : ℕ) : ℤ) ^ 2 - ∑ i, (j i : ℤ) ^ 2
      + 2 * ((∑ i, j i : ℕ) : ℤ) * (n - 2 * ((∑ i, j i : ℕ) : ℤ)) := by
    unfold dimN
    push_cast [Nat.cast_sub h, Finset.sum_filter]
    exact h1
  exact_mod_cast h2

theorem cIw_eq (p q a : ℕ) (j : Fin a → ℕ) (hp : ∑ i, j i ≤ p) (hq : ∑ i, j i ≤ q) :
    cIw p q j = (2 : ℝ) ^ (-((dimN (p + q) j : ℝ) / 2) + (((p : ℝ) + q) * ((∑ i, j i : ℕ) : ℝ)
        - ((∑ i, j i : ℕ) : ℝ) ^ 2 - ((∑ i, j i : ℕ) : ℝ) / 2 - ∑ i, (j i : ℝ) ^ 2)) *
      (sphV p * sphV q / (sphV (p - ∑ i, j i) * sphV (q - ∑ i, j i) * ∏ i, sphV (j i))) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hP : (∏ i, GlobalTheory.FlagMeas.volU (j i) * (2 : ℝ) ^ (((j i : ℝ)) ^ 2 / 2)) =
      (∏ i, sphV (j i)) * (2 : ℝ) ^ (∑ i, (j i : ℝ) ^ 2 - ((∑ i, j i : ℕ) : ℝ) / 2) := by
    simp only [volU_eq, mul_assoc, ← Real.rpow_add h2]
    rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos h2]
    congr 2
    push_cast
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold cIw
  rw [hP]
  simp only [volU_eq]
  rw [Nat.cast_sub hp, Nat.cast_sub hq]
  generalize ((∑ i, j i : ℕ) : ℝ) = J
  generalize ∑ i, (j i : ℝ) ^ 2 = S
  generalize (dimN (p + q) j : ℝ) = D
  have key : (2 : ℝ) ^ (-(D / 2) + (((p : ℝ) + q) * J - J ^ 2 - J / 2 - S)) =
      (2 : ℝ) ^ (-(D / 2)) * (2 : ℝ) ^ (((p : ℝ) ^ 2 - p) / 2) * (2 : ℝ) ^ (((q : ℝ) ^ 2 - q) / 2) /
      ((2 : ℝ) ^ (S - J / 2) * (2 : ℝ) ^ ((((p : ℝ) - J) ^ 2 - (p - J)) / 2) *
        (2 : ℝ) ^ ((((q : ℝ) - J) ^ 2 - (q - J)) / 2)) := by
    simp only [← Real.rpow_add h2, ← Real.rpow_sub h2]
    congr 1
    ring
  rw [key, div_mul_div_comm]
  congr 1 <;> ring

theorem prod_five_factors : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (p q a : ℕ) (j : Fin a → ℕ), ∑ i, j i ≤ q → 2 * q + 2 ≤ p + q → cIw p q j ^ Formalism.HermitianLatticesTheory.fDeg E * (2 * Formalism.HermitianLatticesTheory.vInv E) ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) * dimN (p + q) j / 2) * (∏ i, 2 ^ (Formalism.HermitianLatticesTheory.fDeg E * j i ^ 2) * (dedekindZeta_residue E * Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * j i ^ 2) * ∏ l ∈ Finset.Icc 2 (j i), zetaE E l)) / ∏ M ∈ Finset.Ioc (p + q - 2 * ∑ i, j i) (p + q), rankFac E M = kapBd E p q j := by
  intro E _ _ _ _ p q a j hq hpq
  have hp : ∑ i, j i ≤ p := by omega
  have hn : 2 * ∑ i, j i ≤ p + q := by omega
  have hv := vInv_pos E
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hD := dimN_eq (p + q) a j hn
  have hmid : (∏ i, (2 : ℝ) ^ (Formalism.HermitianLatticesTheory.fDeg E * j i ^ 2) * (dedekindZeta_residue E *
      Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * j i ^ 2) * ∏ l ∈ Finset.Icc 2 (j i), zetaE E l)) =
      (2 : ℝ) ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) * ∑ i, (j i : ℝ) ^ 2) * (dedekindZeta_residue E ^ a *
      Formalism.HermitianLatticesTheory.vInv E ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) * ∑ i, (j i : ℝ) ^ 2) *
        ∏ i, ∏ l ∈ Finset.Icc 2 (j i), zetaE E l) := by
    have hc : (Formalism.HermitianLatticesTheory.fDeg E : ℝ) * ∑ i, (j i : ℝ) ^ 2 =
        ((∑ i, Formalism.HermitianLatticesTheory.fDeg E * j i ^ 2 : ℕ) : ℝ) := by
      push_cast
      rw [Finset.mul_sum]
    rw [hc, Real.rpow_natCast, Real.rpow_natCast]
    simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  rw [hmid, prod_rankFac E _ _ (Nat.sub_le _ _), cIw_eq p q a j hp hq, mul_pow,
    ← Real.rpow_mul_natCast h2.le, Nat.cast_sub hn]
  unfold kapBd
  rw [hD]
  push_cast [-Nat.cast_sum]
  generalize ((∑ i, j i : ℕ) : ℝ) = J
  generalize ∑ i, (j i : ℝ) ^ 2 = S
  generalize (sphV p * sphV q / (sphV (p - ∑ i, j i) * sphV (q - ∑ i, j i) * ∏ i, sphV (j i))) ^
    Formalism.HermitianLatticesTheory.fDeg E = R
  generalize (Formalism.HermitianLatticesTheory.fDeg E : ℝ) = f
  generalize Formalism.HermitianLatticesTheory.vInv E = v at hv ⊢
  generalize ((p : ℝ) + q) = n
  rw [Real.mul_rpow h2.le hv.le, Real.mul_rpow h2.le hv.le, ← div_div]
  congr 1
  have k2 : (2 : ℝ) ^ (-(f * (n * J - J ^ 2 + J / 2))) =
      (2 : ℝ) ^ ((-((2 * J ^ 2 - S + 2 * J * (n - 2 * J)) / 2) + (n * J - J ^ 2 - J / 2 - S)) * f) *
      (2 : ℝ) ^ (f * (2 * J ^ 2 - S + 2 * J * (n - 2 * J)) / 2) * (2 : ℝ) ^ (f * S) /
      (2 : ℝ) ^ (f * ((n ^ 2 - (n - 2 * J) ^ 2) / 2)) := by
    simp only [← Real.rpow_add h2, ← Real.rpow_sub h2]
    congr 1
    ring
  have kv : v ^ (-(f * (2 * J ^ 2 - S + 2 * J * (n - 2 * J)) / 2)) =
      v ^ (f * (2 * J ^ 2 - S + 2 * J * (n - 2 * J)) / 2) * v ^ (f * S) /
      v ^ (f * ((n ^ 2 - (n - 2 * J) ^ 2) / 2)) := by
    simp only [← Real.rpow_add hv, ← Real.rpow_sub hv]
    congr 1
    ring
  rw [k2, kv]
  field_simp

end GlobalTheory.FiveFactors
