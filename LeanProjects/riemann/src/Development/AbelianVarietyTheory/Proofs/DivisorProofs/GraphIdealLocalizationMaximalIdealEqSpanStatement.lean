import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GraphIdealLocalizationMaximalIdealEqSpan
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToQMemMaximalIdealIff
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graphIdeal_localization_maximalIdeal_eq_span : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    [Algebra (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (k : ℕ) (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (hER : E.Contains R) (t : E.ring) (zR : Fin k → R)
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime],
  (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) → (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  Irreducible t → TrBasis (algebraMap ℂ κ) (fun i => π (zR i)) →
  𝔭 ∈ (graphIdeal E R π ρ).minimalPrimes →
  letI := isLocalRing_locAt (L := L) 𝔭 (IsFractionRing.injective (K ⊗[ℂ] κ') L)
  IsLocalRing.maximalIdeal (locAt (L := L) 𝔭) =
    Ideal.span (Set.range fun i => toQ 𝔭 (gens E R π ρ hER t zR i)) := by
  first | exact @GlobalTheory.GraphLocal.MaxGen.maximalIdeal_locAt_eq_span | exact GlobalTheory.GraphLocal.MaxGen.maximalIdeal_locAt_eq_span | (intros; apply GlobalTheory.GraphLocal.MaxGen.maximalIdeal_locAt_eq_span <;> assumption)
