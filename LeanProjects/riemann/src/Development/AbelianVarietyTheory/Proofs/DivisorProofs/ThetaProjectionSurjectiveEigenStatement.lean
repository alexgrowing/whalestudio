import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaProjectionSurjectiveEigen
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_projection_surjective_eigen : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (C : Type) [Field C] [Algebra O C] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (σ : Λ →+* O) (f : RL p O Λ →+* O) (ρ : Λ → Matrix (Fin h) (Fin h) (Ainf p O)) (e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)) (π : (Fin h → C) →ₗ[C] (Fin N → C)), Function.Injective (algebraMap O C) → Function.Surjective (WittVector.fontaineTheta O p) → Function.Surjective f → IsTheta σ f → IsFrame ρ e → IsProj C e f π → (⨆ s : Λ →+* O, eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) s) = ⊤ → Module.finrank C (eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) σ) = N → ∃ q : eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) σ ≃ₗ[C] (Fin N → C), (∀ x, q x = π x) ∧ ∀ x, x ∈ quotLattice C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) σ ↔ ∀ i, q x i ∈ (algebraMap O C).range := by
  first | exact @GlobalTheory.DetInv.projEigenspaceEquiv | exact GlobalTheory.DetInv.projEigenspaceEquiv | (intros; apply GlobalTheory.DetInv.projEigenspaceEquiv <;> assumption)
