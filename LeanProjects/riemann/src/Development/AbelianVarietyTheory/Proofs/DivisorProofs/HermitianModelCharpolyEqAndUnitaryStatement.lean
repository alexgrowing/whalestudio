import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianModelCharpolyEqAndUnitary
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
open GlobalTheory.UnitLemma Polynomial Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianModel_charpoly_eq_and_unitary : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (γ : Matrix (Fin n) (Fin n) K.E) (x : B.Aˣ) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B γ x ψ → γ.charpoly = B.P ∧ (B.g * B.σ B.g = 1 → (γ.map K.c)ᵀ * γ = 1) := by
  first | exact @GlobalTheory.ModelCharpoly.model_charpoly_unitary | exact GlobalTheory.ModelCharpoly.model_charpoly_unitary | (intros; apply GlobalTheory.ModelCharpoly.model_charpoly_unitary <;> assumption)
