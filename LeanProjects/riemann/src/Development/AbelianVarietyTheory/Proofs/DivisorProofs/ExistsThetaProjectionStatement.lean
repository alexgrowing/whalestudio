import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaProjection
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_projection : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (C : Type) [Field C] [Algebra O C] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (σ : Λ →+* O) (f : RL p O Λ →+* O) (e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)), IsTheta σ f → ∃ π, IsProj C e f π := by
  first | exact @GlobalTheory.DetInv.proj_exists | exact GlobalTheory.DetInv.proj_exists | (intros; apply GlobalTheory.DetInv.proj_exists <;> assumption)
