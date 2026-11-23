import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBcInvariantUnderScaling
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
theorem _root_.GlobalTheory.T.flag_bc_invariant_under_scaling : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {E : X.Modules} {r : ℕ} {h : VMetric p E r} (H : h.IsCInf) (fl : Vert.Flag E r) (s : ℝ), ((h.scale s).FlagBcFinite fl ↔ h.FlagBcFinite fl) ∧ (h.scale s).flagBc fl = h.flagBc fl := by
  first | exact @GlobalTheory.BcScale.flagBc_scale | exact GlobalTheory.BcScale.flagBc_scale | (intros; apply GlobalTheory.BcScale.flagBc_scale <;> assumption)
