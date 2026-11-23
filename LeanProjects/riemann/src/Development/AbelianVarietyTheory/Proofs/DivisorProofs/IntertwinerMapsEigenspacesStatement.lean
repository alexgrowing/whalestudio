import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwinerMapsEigenspaces
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intertwiner_maps_eigenspaces : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h : ℕ) (ρ ρ' : Λ → Matrix (Fin h) (Fin h) O) (X : Matrix (Fin h) (Fin h) O), (∀ l, X * ρ l = ρ' l * X) → (∀ σ : Λ →+* O, (eig C ρ σ).map (Matrix.toLin' (X.map (algebraMap O C))) ≤ eig C ρ' σ) ∧ ((⨆ σ : Λ →+* O, eig C ρ σ) = ⊤ → iSupIndep (fun σ : Λ →+* O => eig C ρ' σ) → ∀ σ : Λ →+* O, LinearMap.range (Matrix.toLin' (X.map (algebraMap O C))) ⊓ eig C ρ' σ = (eig C ρ σ).map (Matrix.toLin' (X.map (algebraMap O C)))) := by
  first | exact @GlobalTheory.DetInv.eig_map_equivariant | exact GlobalTheory.DetInv.eig_map_equivariant | (intros; apply GlobalTheory.DetInv.eig_map_equivariant <;> assumption)
