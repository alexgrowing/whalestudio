import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularEverywhereIsIntegral
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_everywhere_isIntegral : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → Function.Injective (algebraMap O Ω) → IsCptGen ξ → ∀ a : Ω, ((∀ p : Cpt ξ, a ∈ regAt ξ p) → IsIntegral O a) ∧ ((∀ p ∈ genFibre O ξ, a ∈ regAt ξ p) → IsAlgebraic O a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.isIntegral_and_isAlgebraic_of_regular | exact GlobalTheory.CompanionTheory.Ar.Flat.isIntegral_and_isAlgebraic_of_regular | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.isIntegral_and_isAlgebraic_of_regular <;> assumption)
