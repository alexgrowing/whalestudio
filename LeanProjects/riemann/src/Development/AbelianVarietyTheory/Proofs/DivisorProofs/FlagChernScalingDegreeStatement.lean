import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagChernScalingDegree
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
theorem _root_.GlobalTheory.T.flag_chern_scaling_degree : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) [IsIntegral S], IsRegSurf p → ∀ (E : S.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf) (fl : Vert.Flag E r) (a s : ℝ), VMetric.IsFlagCh2 H fl a → VMetric.IsFlagCh2 (H.scale s) fl (a - s / 2 * gdeg (VMetric.det H) 1) := by
  first | exact @GlobalTheory.FlagScale.isFlagCh2_scale | exact GlobalTheory.FlagScale.isFlagCh2_scale | (intros; apply GlobalTheory.FlagScale.isFlagCh2_scale <;> assumption)
