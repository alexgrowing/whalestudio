import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetLineCoordinateIso
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_det_line_coordinate_iso : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h N : ℕ) (ρ : Λ → Matrix (Fin h) (Fin h) O) (σ : Λ →+* O) (q : eig C ρ σ ≃ₗ[C] (Fin N → C)), (∀ x, x ∈ quotLattice C ρ σ ↔ ∀ i, q x i ∈ (algebraMap O C).range) → ∃ δ : detLine C ρ σ N ≃ₗ[C] C, (∀ x : Fin N → eig C ρ σ, δ (exteriorPower.ιMulti C N x) = (Matrix.of fun i => q (x i)).det) ∧ ∀ w, w ∈ detLattice C ρ σ N ↔ δ w ∈ (algebraMap O C).range := by
  first | exact @GlobalTheory.detLine_coord | exact GlobalTheory.detLine_coord | (intros; apply GlobalTheory.detLine_coord <;> assumption)
