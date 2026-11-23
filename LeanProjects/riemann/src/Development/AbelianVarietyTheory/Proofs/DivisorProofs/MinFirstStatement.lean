import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinFirst
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_jointHarm_highestWeight_and_map_mem_genSub : ∀ (p q r s : ℕ) (M1 : GKMod p q) (M2 : GKMod r s) (f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ M1.V M2.V), IrrGK M1 → AdmGK M1 → Intw M1 M2 f → f ≠ 0 → ∀ (μ : Ix p q → ℚ), (∃ v, IsHW M1.act μ v) → (∀ ν w, IsHW M1.act ν w → degW (cPair r s) μ ≤ degW (cPair r s) ν) → (∃ (μ' : Ix r s → ℚ) (P : Pol p q r s), P ∈ jointHarm p q r s ∧ IsHW (fockAct1 p q r s) μ P ∧ IsHW (fockAct2 p q r s) μ' P ∧ f P ≠ 0) ∧ ∀ P, OfType (fockAct1 p q r s) μ P → f P ∈ Submodule.map f (genSub (fockAct2 p q r s) {Q | Q ∈ jointHarm p q r s ∧ OfType (fockAct1 p q r s) μ Q}) := by
  first | exact @GlobalTheory.FockAlg.min_first | exact GlobalTheory.FockAlg.min_first | (intros; apply GlobalTheory.FockAlg.min_first <;> assumption)
