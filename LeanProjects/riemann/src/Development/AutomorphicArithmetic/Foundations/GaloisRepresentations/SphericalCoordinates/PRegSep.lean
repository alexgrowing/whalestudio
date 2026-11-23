import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolyOfRegAfOfFixL
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.regSep_of :
    UpperTheory.Gal.W2.RegSep := by
  intro p _ D G L v hv B a y hfix hreg
  exact GlobalTheory.LKCx.minpoly_of_regAf_of_fixL p G v hv B.β B.sym B.trivR _ _
    B.trivAf.choose_spec.choose_spec y a.1.1 a.2 hfix hreg
