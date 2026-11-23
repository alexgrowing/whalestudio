import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPlaceWeightConjInvariant
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_place_weight_conj_invariant : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (t : (F →+* ℂ) → ℝ), OverInt y φ → ∃ u, IsPlaceWeight y φ t u ∧ ((∀ σ, t (ComplexEmbedding.conjugate σ) = t σ) → ∀ z : (Σ k, ι k) → ℂ, u (fun p => (starRingEnd ℂ) (z p)) = u z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_placeWeight | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_placeWeight | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_placeWeight <;> assumption)
