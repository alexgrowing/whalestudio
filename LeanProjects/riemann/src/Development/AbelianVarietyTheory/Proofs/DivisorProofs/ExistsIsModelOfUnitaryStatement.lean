import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsModelOfUnitary
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
open GlobalTheory.UnitLemma Polynomial Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isModel_of_unitary_charpoly_eq : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (γ : Matrix (Fin n) (Fin n) K.E), (γ.map K.c)ᵀ * γ = 1 → B.g * B.σ B.g = 1 → B.P.Separable → γ.charpoly = B.P → ∃ (x : B.Aˣ) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B γ x ψ := by
  first | exact @GlobalTheory.InertUnitOrb.exists_isModel_of_unitary | exact GlobalTheory.InertUnitOrb.exists_isModel_of_unitary | (intros; apply GlobalTheory.InertUnitOrb.exists_isModel_of_unitary <;> assumption)
