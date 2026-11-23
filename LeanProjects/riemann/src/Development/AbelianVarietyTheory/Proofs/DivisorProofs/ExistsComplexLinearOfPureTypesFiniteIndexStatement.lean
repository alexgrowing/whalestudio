import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexLinearOfPureTypesFiniteIndex
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complexLinear_of_pure_types_finite_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (P' : D'.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (hP' : IsPeriod D' ty P') (Φ : D.La ≃ₗ[𝓞 E] D'.La) (N : ℕ), 0 < N → (∀ v : D.La, N • v ∈ lat hP H.rt0 ⊔ lat hP (-H.rt0)) → (∀ a ∈ lat hP H.rt0, Φ a ∈ lat hP' H.rt0) → (∀ a ∈ lat hP (-H.rt0), Φ a ∈ lat hP' (-H.rt0)) → ∃ L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ a, P' (Φ a) = L (P a) := by
  first | exact @GlobalTheory.CompRat.exists_complex_linear_of_pure_types_of_index | exact GlobalTheory.CompRat.exists_complex_linear_of_pure_types_of_index | (intros; apply GlobalTheory.CompRat.exists_complex_linear_of_pure_types_of_index <;> assumption)
