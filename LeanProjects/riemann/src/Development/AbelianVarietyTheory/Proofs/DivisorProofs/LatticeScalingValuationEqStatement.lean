import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeScalingValuationEq
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_scaling_valuation_eq : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (V W : Type) [AddCommGroup V] [Module C V] [AddCommGroup W] [Module C W] (LV : Set V) (LW : Set W) (δ : V ≃ₗ[C] C) (δ' : W ≃ₗ[C] C) (ι : V →ₗ[C] W) (lam : C), v.Integers O → (∀ w, w ∈ LV ↔ δ w ∈ (algebraMap O C).range) → (∀ w, w ∈ LW ↔ δ' w ∈ (algebraMap O C).range) → ι '' LV = (fun w => lam • w) '' LW → ∃ l₀ : C, v l₀ = v lam ∧ ∀ w, δ' (ι w) = l₀ * δ w := by
  first | exact @GlobalTheory.DetInv.scalar_of_lattice_image | exact GlobalTheory.DetInv.scalar_of_lattice_image | (intros; apply GlobalTheory.DetInv.scalar_of_lattice_image <;> assumption)
