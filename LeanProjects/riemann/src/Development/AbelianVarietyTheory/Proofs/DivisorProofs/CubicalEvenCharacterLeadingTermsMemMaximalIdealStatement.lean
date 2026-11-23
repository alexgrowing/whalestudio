import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalEvenCharacterLeadingTermsMemMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubical_even_character_leading_terms_mem_maximalIdeal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (κ : X → (FractionRing R)ˣ), (∀ a, κ (-a) = κ a) → (∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b)) → (∀ a, a ≠ 0 → ∃ s ∈ maximalIdeal R, (κ a : FractionRing R) = algebraMap R _ s) → ∀ α : X, ∃ k₀ : ℕ, ∀ k ≥ k₀, (∀ m, m ≠ 0 → ∃ s ∈ maximalIdeal R, ((κ m ^ k * (κ (m + α) * (κ m)⁻¹ * (κ α)⁻¹) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ s) ∧ ∀ n : ℕ, {m | ¬ ∃ s ∈ maximalIdeal R ^ n, ((κ m ^ k * (κ (m + α) * (κ m)⁻¹ * (κ α)⁻¹) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ s}.Finite := by
  first | exact @GlobalTheory.LeadTerm.lead_mem | exact GlobalTheory.LeadTerm.lead_mem | (intros; apply GlobalTheory.LeadTerm.lead_mem <;> assumption)
