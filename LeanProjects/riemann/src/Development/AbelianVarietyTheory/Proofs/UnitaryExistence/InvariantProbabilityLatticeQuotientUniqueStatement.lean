import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InvariantProbabilityLatticeQuotientUnique
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_probability_lattice_quotient_unique : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 ≠ ⊤ → ∀ (ν : Measure (Quotient (QuotientGroup.rightRel Γ))) [IsProbabilityMeasure ν], (∀ (h : G) (ρ : Quotient (QuotientGroup.rightRel Γ) → Quotient (QuotientGroup.rightRel Γ)), (∀ g : G, ρ (Quotient.mk _ g) = Quotient.mk _ (g * h)) → ∀ s, MeasurableSet s → ν (ρ ⁻¹' s) = ν s) → ν = (μ 𝓕)⁻¹ • (μ.restrict 𝓕).map (fun g : G => (Quotient.mk _ g : Quotient (QuotientGroup.rightRel Γ))) := by
  first | exact @GlobalTheory.LatticeQuotUniq.invariant_prob_eq | exact GlobalTheory.LatticeQuotUniq.invariant_prob_eq | (intros; apply GlobalTheory.LatticeQuotUniq.invariant_prob_eq <;> assumption)
