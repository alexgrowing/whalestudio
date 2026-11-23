import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepBasisCharpoly
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rep_basis_charpoly : ∀ (p : ℕ) [Fact p.Prime] (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Free ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] (h d : ℕ) (b : Module.Basis (Fin d) ℤ_[p] Λ) (ρ : Λ →ₐ[ℤ_[p]] Matrix (Fin h) (Fin h) ℤ_[p]), ∃ (N : ℕ) (y : Fin N → Fin h → ℤ_[p]), h = N * d ∧ Submodule.span ℤ_[p] (Set.range fun ij : Fin N × Fin d => ρ (b ij.2) *ᵥ y ij.1) = ⊤ ∧ ∀ a : Λ, (ρ a).charpoly = (LinearMap.mulLeft ℤ_[p] a).charpoly ^ N := by
  first | exact @GlobalTheory.DetInv.rep_free_charpoly | exact GlobalTheory.DetInv.rep_free_charpoly | (intros; apply GlobalTheory.DetInv.rep_free_charpoly <;> assumption)
