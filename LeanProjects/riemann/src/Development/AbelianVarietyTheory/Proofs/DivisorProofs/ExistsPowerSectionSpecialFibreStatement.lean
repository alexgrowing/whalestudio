import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowerSectionSpecialFibre
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_power_section_special_fibre : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X],
  (∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) →
  ∀ (π : Γ(X, ⊤)), genericPoint X ∈ X.basicOpen π → (∃ z : X, z ∉ X.basicOpen π) →
  ∀ (L : LB X) (τ : L.ι → X.functionFieldˣ), L.IsLB → IsRatSec L τ →
    (∀ (i : L.ι) (z : X), z ∈ L.U i → z ∈ X.basicOpen π → UnitAt z (τ i : X.functionField)) →
    ∃ (M : ℕ) (n : ℤ) (x₀ : X), 1 ≤ M ∧ x₀ ∉ X.basicOpen π ∧
      (∀ (i : L.ι) (z : X), z ∈ L.U i → IsDiscreteValuationRing (X.presheaf.stalk z) →
        RegAt z (fnOf ⊤ trivial π ^ n * ((τ i : X.functionField) ^ M)⁻¹)) ∧
      (∀ i : L.ι, x₀ ∈ L.U i → UnitAt x₀ (fnOf ⊤ trivial π ^ n * ((τ i : X.functionField) ^ M)⁻¹)) := by
  first | exact @GlobalTheory.ExpChoice.exists_exponents | exact GlobalTheory.ExpChoice.exists_exponents | (intros; apply GlobalTheory.ExpChoice.exists_exponents <;> assumption)
