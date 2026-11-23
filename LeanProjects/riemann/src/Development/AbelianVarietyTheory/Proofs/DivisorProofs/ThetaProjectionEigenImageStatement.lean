import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaProjectionEigenImage
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_projection_eigen_image : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (C : Type) [Field C] [Algebra O C] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (σ : Λ →+* O) (f : RL p O Λ →+* O) (ρ : Λ → Matrix (Fin h) (Fin h) (Ainf p O)) (e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)) (π : (Fin h → C) →ₗ[C] (Fin N → C)), Function.Injective (algebraMap O C) → IsTheta σ f → IsFrame ρ e → IsProj C e f π → ∀ z ∈ ⨆ s : {s : Λ →+* O // s ≠ σ}, eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) s.1, π z = 0 := by
  first | exact @GlobalTheory.DetInv.proj_kills_other_eig | exact GlobalTheory.DetInv.proj_kills_other_eig | (intros; apply GlobalTheory.DetInv.proj_kills_other_eig <;> assumption)
