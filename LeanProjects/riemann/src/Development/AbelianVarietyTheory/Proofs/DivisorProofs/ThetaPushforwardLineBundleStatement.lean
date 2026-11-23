import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPushforwardLineBundle
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
theorem _root_.GlobalTheory.T.theta_pushforward_line_bundle : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k), IsRegSurf p → ∀ (P : PPAS S) (L : LB P.A.left), IsTheta P L → ∃ M : LB S, M.IsLB ∧ Nonempty (toMod M ≅ (Scheme.Modules.pushforward P.A.hom).obj (toMod L)) := by
  first | exact @GlobalTheory.ThetaRR.exists_lb_pushforward | exact GlobalTheory.ThetaRR.exists_lb_pushforward | (intros; apply GlobalTheory.ThetaRR.exists_lb_pushforward <;> assumption)
