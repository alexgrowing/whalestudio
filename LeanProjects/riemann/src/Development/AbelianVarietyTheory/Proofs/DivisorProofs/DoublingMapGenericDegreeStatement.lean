import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingMapGenericDegree
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubling_map_generic_degree : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k), IsRegSurf p → ∀ (P : PPAS S) (L : LB P.A.left), IsTheta P L → ∀ [IsIntegral P.A.left], dbl P (genericPoint P.A.left) = genericPoint P.A.left ∧ (dbl P).residueDegree (genericPoint P.A.left) = 4 ^ P.g := by
  first | exact @GlobalTheory.DblDegree.dbl_genericPoint_residueDegree | exact GlobalTheory.DblDegree.dbl_genericPoint_residueDegree | (intros; apply GlobalTheory.DblDegree.dbl_genericPoint_residueDegree <;> assumption)
