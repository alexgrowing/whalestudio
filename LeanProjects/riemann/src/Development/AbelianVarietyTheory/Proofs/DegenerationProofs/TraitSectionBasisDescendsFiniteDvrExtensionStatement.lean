import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TraitSectionBasisDescendsFiniteDvrExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trait_sectionBasis_descends_finite_dvr_extension : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left), Flat G.hom → L.IsLB → ∀ (N : ℕ) (K : Type) [Field K] (x : Sp K ⟶ Z) (W W' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing W'] [IsDomain W'] [IsDiscreteValuationRing W'] (io : W →+* W') (io' : FractionRing W →+* FractionRing W'), io.Finite → (∀ y, io' (algebraMap W _ y) = algebraMap W' _ (io y)) → ∀ (gam : K →+* FractionRing W) (χ : Sp W ⟶ Z) (h : spMap gam ≫ x = jK W ≫ χ) (h' : spMap (io'.comp gam) ≫ x = jK W' ≫ spMap io ≫ χ) (n : ℕ) (f : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x))), FrameAt G L N x (io'.comp gam) (spMap io ≫ χ) h' f → FrameAt G L N x gam χ h f := by
  first | exact @GlobalTheory.OneBasis.TraitDescent.frameAt_of_finite | exact GlobalTheory.OneBasis.TraitDescent.frameAt_of_finite | (intros; apply GlobalTheory.OneBasis.TraitDescent.frameAt_of_finite <;> assumption)
