import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RelAmpleNearFibreFlatProjective
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_near_fibre_flat_projective : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (B : Over (Spec (CommRingCat.of R))) (L : LB B.left), Flat B.hom → IsProjBy B.hom → L.IsLB → ∀ (K : Type) [Field K] (g : R →+* K), (∀ y : K, ∃ a b : R, g b ≠ 0 ∧ y * g b = g a) → RelAmple ((Over.pullback (Spec.map (CommRingCat.ofHom g))).obj B) (L.pull (pullback.fst B.hom (Spec.map (CommRingCat.ofHom g)))) → ∃ r : R, g r ≠ 0 ∧ RelAmple ((Over.pullback (Scheme.Opens.ι (X := Spec (CommRingCat.of R)) (PrimeSpectrum.basicOpen r))).obj B) (L.pull (pullback.fst B.hom (Scheme.Opens.ι (X := Spec (CommRingCat.of R)) (PrimeSpectrum.basicOpen r)))) := by
  first | exact @GlobalTheory.AmpleNear.relAmple_near_fibre | exact GlobalTheory.AmpleNear.relAmple_near_fibre | (intros; apply GlobalTheory.AmpleNear.relAmple_near_fibre <;> assumption)
