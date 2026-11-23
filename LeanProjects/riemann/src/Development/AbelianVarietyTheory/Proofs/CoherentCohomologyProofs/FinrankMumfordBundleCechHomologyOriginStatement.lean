import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FinrankMumfordBundleCechHomologyOrigin
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_mumfordBundle_cech_homology_origin : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ P.A.left) (Y : Scheme.{0}) (π : Y ⟶ (P.A ⊗ P.A).left) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f (fst P.A P.A).left t → IsOpenImmersion t → (∃ p q, t p = η[P.A].left q) → ∀ D : Fin (P.g + 1) → Y.Opens, (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ∀ n, Module.Finite K ((cechLB (f ≫ t ≫ P.A.hom) ((translDiff P.A P.L (𝟙 P.A)).pull π) D).homology n) ∧ Module.finrank K ((cechLB (f ≫ t ≫ P.A.hom) ((translDiff P.A P.L (𝟙 P.A)).pull π) D).homology n) = if n = P.g then 1 else 0 := by
  first | exact @GlobalTheory.OriginCohom.finrank_cechLB_homology | exact GlobalTheory.OriginCohom.finrank_cechLB_homology | (intros; apply GlobalTheory.OriginCohom.finrank_cechLB_homology <;> assumption)
