import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumLineMatrixKroneckerRightFactor

noncomputable section
namespace GlobalTheory.FockLowDiff
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

def ixSign {p q : ℕ} : Ix p q → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)

theorem Jm_eq_diagonal (p q : ℕ) : Jm p q = Matrix.diagonal ixSign := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Jm, Formalism.UG.Jpq, ixSign, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem omAct_kron_diagonal {p q r s : ℕ} (Z : Mat p q) (t : Ix r s → ℂ) (P : Pol p q r s) :
    omAct p q r s (Matrix.kroneckerMap (· * ·) Z (Matrix.diagonal t)) P =
      ∑ a, ∑ b, ∑ c, (Z a b * t c) • omE ((a, c) : Ln p q r s) (b, c) P := by
  rw [omAct_apply, Fintype.sum_prod_type, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm (f := fun b c => (Z a b * t c) • omE ((a, c) : Ln p q r s) (b, c) P),
    LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Fintype.sum_prod_type, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [LinearMap.sum_apply, Finset.sum_eq_single c]
  · simp
  · intro d _ hd
    simp [Matrix.diagonal_apply_ne _ (Ne.symm hd)]
  · simp

theorem lowering_eq_diff : ∀ (p q r s : ℕ) (Z : Mat p q), IsPC Z → ∀ P : Pol p q r s, omAct p q r s (Matrix.kroneckerMap (· * ·) Z (1 : Mat r s)) P - omAct p q r s (Matrix.kroneckerMap (· * ·) (Jm p q * Z) (Jm r s)) P = (2 : ℂ) • minusPart (fockAct1 p q r s Z) P := by
  intro p q r s Z hZ P
  rw [((GlobalTheory.FockParts.explicit_parts p q r s).1 Z hZ P).2, Jm_eq_diagonal, Jm_eq_diagonal,
    ← Matrix.diagonal_one, omAct_kron_diagonal, omAct_kron_diagonal, ← Finset.sum_sub_distrib,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.diagonal_mul, ← sub_smul]
  by_cases hab : sameBlock a b
  · simp [hZ a b hab]
  · rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
      simp [sameBlock] at hab <;>
      simp [ixSign, linePos, omE, raiB, lowB, two_smul, add_smul, add_comm]

end GlobalTheory.FockLowDiff
