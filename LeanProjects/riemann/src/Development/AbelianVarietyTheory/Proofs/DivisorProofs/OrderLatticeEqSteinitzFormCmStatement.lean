import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderLatticeEqSteinitzFormCm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableRisingS
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orderLattice_eq_steinitzForm_cm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ → ∀ θ : E, θ ∉ maximalRealSubfield E → ∃ (𝔞 𝔟 : Frac (maximalRealSubfield E)) (a₀ : maximalRealSubfield E), ∀ x : E, x ∈ lattice c y ↔ ∃ a ∈ latM 𝔞, ∃ b ∈ (𝔟 : FractionalIdeal (𝓞 (maximalRealSubfield E))⁰ (maximalRealSubfield E)), x = (a : E) + (b : E) * (θ + (a₀ : E)) := by
  first | exact @GlobalTheory.SteinitzOrder.lattice_eq_steinitz | exact GlobalTheory.SteinitzOrder.lattice_eq_steinitz | (intros; apply GlobalTheory.SteinitzOrder.lattice_eq_steinitz <;> assumption)
