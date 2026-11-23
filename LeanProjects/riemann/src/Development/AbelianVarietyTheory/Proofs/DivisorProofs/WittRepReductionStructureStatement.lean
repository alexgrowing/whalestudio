import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRepReductionStructure
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_rep_reduction_structure : ∀ (p : ℕ) [Fact p.Prime] (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Free ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] (k : Type) [Field k] [IsAlgClosed k] [CharP k p] (h d N : ℕ) (b : Module.Basis (Fin d) ℤ_[p] Λ) (s : ℤ_[p] →+* WittVector p k) (ρ : Λ →+* Matrix (Fin h) (Fin h) (WittVector p k)), (∀ c : ℤ_[p], ρ (algebraMap ℤ_[p] Λ c) = s c • (1 : Matrix (Fin h) (Fin h) (WittVector p k))) → (∀ a : Λ, (ρ a).charpoly = ((LinearMap.mulLeft ℤ_[p] a).charpoly ^ N).map s) → ∃ x : Fin N → Fin h → k, Submodule.span k (Set.range fun ij : Fin N × Fin d => (ρ (b ij.2)).map WittVector.constantCoeff *ᵥ x ij.1) = ⊤ := by
  first | exact @GlobalTheory.DetInv.special_fibre_generators | exact GlobalTheory.DetInv.special_fibre_generators | (intros; apply GlobalTheory.DetInv.special_fibre_generators <;> assumption)
