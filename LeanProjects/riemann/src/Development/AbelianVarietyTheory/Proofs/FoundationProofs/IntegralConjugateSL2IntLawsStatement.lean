import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralConjugateSL2IntLaws
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralConjugateSL2Int_laws : (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (M : ℕ), 0 < m.det → ∀ δ ∈ CongruenceSubgroup.Gamma (M * m.det.natAbs), m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (cj m δ : Matrix (Fin 2) (Fin 2) ℤ) * m ∧ cj m δ ∈ CongruenceSubgroup.Gamma M) ∧ (∀ γ δ : SL(2, ℤ), cj (γ : Matrix (Fin 2) (Fin 2) ℤ) δ = γ * δ * γ⁻¹) ∧ (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (δ δ' : SL(2, ℤ)), 0 < m.det → m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * m → ∀ z ∈ Hs, mob (toGQ m) (mob (ofSL δ) z) = mob (ofSL δ') (mob (toGQ m) z)) := by
  first | exact @GlobalTheory.KZ.cj_laws | exact GlobalTheory.KZ.cj_laws | (intros; apply GlobalTheory.KZ.cj_laws <;> assumption)
