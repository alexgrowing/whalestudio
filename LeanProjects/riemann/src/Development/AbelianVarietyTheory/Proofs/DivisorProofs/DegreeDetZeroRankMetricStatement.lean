import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeDetZeroRankMetric
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticFunctionalQuadraticRelations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricShortExactIsometric
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_det_zero_rank_metric : ∀ (HC : GlobalTheory.Published.ArCalc) {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (hp : IsArithVar p 1) {E : X.Modules} {h : VMetric p E 0} (H : h.IsCInf), gdeg (VMetric.det H) 1 = 0 := by
  first | exact @GlobalTheory.ThetaRR.gdeg_det_rank_zero | exact GlobalTheory.ThetaRR.gdeg_det_rank_zero | (intros; apply GlobalTheory.ThetaRR.gdeg_det_rank_zero <;> assumption)
