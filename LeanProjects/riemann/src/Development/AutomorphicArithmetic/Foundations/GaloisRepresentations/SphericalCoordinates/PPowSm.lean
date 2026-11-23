import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.HeckeFixedPointCMCycleClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothOfRelativeDimensionFibrePower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartBundleQuotientEquivalence

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.powSm_of :
    UpperTheory.Gal.W2.PowSm := by
  intro X s d g hs hqc hsep A _ _ hA hg k
  have hP : IsProper (KS.pow A k).hom := KS.Leray.isProper_pow_hom A hA.proper k
  have hsm := FibPow.smoothOfRelativeDimension_fibrePower ℂ X s d g hs A hA hg k
  refine ⟨hsm, ?_, ?_, ?_⟩
  · infer_instance
  · infer_instance
  · haveI : Smooth ((KS.pow A k).hom ≫ s) := hsm.smooth
    infer_instance
