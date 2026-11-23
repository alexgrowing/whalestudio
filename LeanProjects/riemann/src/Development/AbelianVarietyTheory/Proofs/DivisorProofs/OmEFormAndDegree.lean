import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC

noncomputable section
namespace GlobalTheory.FockOm
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem omE_form_and_degree : ∀ (p q r s : ℕ) (l l' : Ln p q r s) (d : ℕ) (P : Pol p q r s), P ∈ homog (Ix p q × Ix r s) d → (linePos l = linePos l' → omE l l' P ∈ homog (Ix p q × Ix r s) d) ∧ (linePos l = true → linePos l' = false → omE l l' P = X l * X l' * P) ∧ (linePos l = false → linePos l' = true → omE l l' P = - pderiv l (pderiv l' P)) := by
  intro p q r s l l' d P hP
  refine ⟨fun h => GlobalTheory.FockDeg.omE_mem_homog h hP, fun hl hl' => ?_, fun hl hl' => ?_⟩
  · have hne : l ≠ l' := fun e => by rw [e, hl'] at hl; exact absurd hl (by simp)
    simp [omE, raiB, lowB, hl, hl', hne, mul_assoc]
  · have hne : l ≠ l' := fun e => by rw [e, hl'] at hl; exact absurd hl (by simp)
    simp [omE, raiB, lowB, hl, hl', hne]

end GlobalTheory.FockOm
