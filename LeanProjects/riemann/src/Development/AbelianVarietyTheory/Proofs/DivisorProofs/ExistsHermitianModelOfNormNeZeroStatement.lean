import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianModelOfNormNeZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
open GlobalTheory.UnitLemma Polynomial Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitianModel_of_norm_ne_zero : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (x : B.Aˣ), Module.finrank K.E B.A = n → B.σ (x : B.A) = x → B.N x ≠ 0 → ∃ (γ : Matrix (Fin n) (Fin n) K.E) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B γ x ψ := by
  first | exact @GlobalTheory.InertUnitOrb.ModelOfN.exists_model | exact GlobalTheory.InertUnitOrb.ModelOfN.exists_model | (intros; apply GlobalTheory.InertUnitOrb.ModelOfN.exists_model <;> assumption)
