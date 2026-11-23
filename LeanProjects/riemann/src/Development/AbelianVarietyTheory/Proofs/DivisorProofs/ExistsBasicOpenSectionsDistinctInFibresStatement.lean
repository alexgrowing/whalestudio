import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenSectionsDistinctInFibres
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_sections_distinct_in_fibres : ∀ (R : Type) [CommRing R] (X : Over (Sp R)), IsSeparated X.hom → ∀ (K : Type) [Field K] (e : R →+* K), Function.Injective e → ∀ t : Finset (Sp R ⟶ X.left), (∀ x ∈ t, x ≫ X.hom = 𝟙 _) → (∀ x ∈ t, ∀ y ∈ t, x ≠ y → spMap e ≫ x ≠ spMap e ≫ y) → ∃ f : R, e f ≠ 0 ∧ ∀ (F : Type) [Field F] (ψ : R →+* F), IsUnit (ψ f) → ∀ x ∈ t, ∀ y ∈ t, x ≠ y → spMap ψ ≫ x ≠ spMap ψ ≫ y := by
  first | exact @GlobalTheory.SectionsSpread.pairs | exact GlobalTheory.SectionsSpread.pairs | (intros; apply GlobalTheory.SectionsSpread.pairs <;> assumption)
