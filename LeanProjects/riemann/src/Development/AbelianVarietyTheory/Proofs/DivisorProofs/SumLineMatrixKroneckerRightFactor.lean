import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC

noncomputable section
namespace GlobalTheory.FockParts
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial GlobalTheory.FockDeg

variable {p q r s : ℕ}

theorem sum_lineMatrixKroneckerLeftFactor (Z : Mat p q) (F : Ln p q r s → Ln p q r s → ℂ → Pol p q r s)
    (hF : ∀ l l', F l l' 0 = 0) :
    ∑ l, ∑ l', F l l' (kr1 r s Z l l') = ∑ a, ∑ b, ∑ c, F (a, c) (b, c) (Z a b) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm (f := fun b c => F (a, c) (b, c) (Z a b))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single c]
  · simp [kr1]
  · intro d _ hd
    simp [kr1, Ne.symm hd, hF]
  · simp

theorem sum_lineMatrixKroneckerRightFactor (Z : Mat r s) (F : Ln p q r s → Ln p q r s → ℂ → Pol p q r s)
    (hF : ∀ l l', F l l' 0 = 0) :
    ∑ l, ∑ l', F l l' (kr2 p q Z l l') = ∑ c, ∑ d, ∑ a, F (a, c) (a, d) (Z c d) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm (f := fun d a => F (a, c) (a, d) (Z c d))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp [kr2]
  · intro b _ hb
    simp [kr2, Ne.symm hb, hF]
  · simp

theorem explicit_parts : ∀ (p q r s : ℕ), (∀ Z : Mat p q, IsPC Z → ∀ P : Pol p q r s, plusPart (fockAct1 p q r s Z) P = ∑ a, ∑ b, ∑ c, (if linePos ((a, c) : Ln p q r s) = true then Z a b • (X (a, c) * X (b, c) * P) else 0) ∧ minusPart (fockAct1 p q r s Z) P = ∑ a, ∑ b, ∑ c, (if linePos ((a, c) : Ln p q r s) = true then 0 else -(Z a b • pderiv (a, c) (pderiv (b, c) P)))) ∧ (∀ Z : Mat r s, IsPC Z → ∀ P : Pol p q r s, plusPart (fockAct2 p q r s Z) P = ∑ c, ∑ d, ∑ a, (if linePos ((a, c) : Ln p q r s) = true then Z c d • (X (a, c) * X (a, d) * P) else 0) ∧ minusPart (fockAct2 p q r s Z) P = ∑ c, ∑ d, ∑ a, (if linePos ((a, c) : Ln p q r s) = true then 0 else -(Z c d • pderiv (a, c) (pderiv (a, d) P)))) := by
  intro p q r s
  refine ⟨fun Z hZ P => ⟨?_, ?_⟩, fun Z hZ P => ⟨?_, ?_⟩⟩
  · rw [fockAct1_eq, plusPart_omAct (lineMatrixKroneckerLeftFactor_eq_zero_of_isPC hZ), upOp_apply,
      sum_lineMatrixKroneckerLeftFactor Z (fun l l' z => (if linePos l then z else 0) • (X l * X l' * P)) (by simp)]
    simp only [ite_smul, zero_smul]
  · rw [fockAct1_eq, minusPart_omAct (lineMatrixKroneckerLeftFactor_eq_zero_of_isPC hZ), downOp_apply,
      sum_lineMatrixKroneckerLeftFactor Z (fun l l' z => (if linePos l then 0 else -z) • pderiv l (pderiv l' P)) (by simp)]
    simp only [ite_smul, zero_smul, neg_smul]
  · rw [fockAct2_eq, plusPart_omAct (lineMatrixKroneckerRightFactor_eq_zero_of_isPC hZ), upOp_apply,
      sum_lineMatrixKroneckerRightFactor Z (fun l l' z => (if linePos l then z else 0) • (X l * X l' * P)) (by simp)]
    simp only [ite_smul, zero_smul]
  · rw [fockAct2_eq, minusPart_omAct (lineMatrixKroneckerRightFactor_eq_zero_of_isPC hZ), downOp_apply,
      sum_lineMatrixKroneckerRightFactor Z (fun l l' z => (if linePos l then 0 else -z) • pderiv l (pderiv l' P)) (by simp)]
    simp only [ite_smul, zero_smul, neg_smul]

end GlobalTheory.FockParts
