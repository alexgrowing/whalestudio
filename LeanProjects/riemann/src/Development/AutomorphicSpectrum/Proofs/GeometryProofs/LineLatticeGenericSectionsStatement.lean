import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineLatticeGenericSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_lattice_generic_sections : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → Function.Injective (algebraMap O Ω) → IsCptGen ξ → ConstClosed O Ω → ∀ (L : Lat ξ Ω) (t : Ω), (∀ p ∈ genFibre O ξ, L.IsGenAt p t) → ∀ u : Ω, (∀ p ∈ genFibre O ξ, u ∈ L p) ↔ ∃ x y : O, y ≠ 0 ∧ u * algebraMap O Ω y = algebraMap O Ω x * t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.mem_lat_genFibre_iff_const_mul | exact GlobalTheory.CompanionTheory.Ar.Flat.mem_lat_genFibre_iff_const_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.mem_lat_genFibre_iff_const_mul <;> assumption)
