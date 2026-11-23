import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumTwistByCharacter
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFormCongrOfEventuallyEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelActionPreservesFlatForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapSymplecticTransform
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapRigidity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricTranslationPullbackFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatCoordsSymplecticPullbackForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcCompHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteQuotientOfIsLatLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPeriodMapSimplyConnectedStatement
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.datum_twist_by_character : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (g : ℕ) (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (M M' : Submodule ℤ (Fl g)) (j : Fl g → Pt E g → ℂ) (h : Pt E g → ℝ), IsDatum B τ M' j h → IsLat M → M ≤ M' → ∀ χ : AddChar (M' ⧸ M.submoduleOf M') ℂ, IsDatum B τ M' (twistFactor M M' χ j) h := by
  first | exact @GlobalTheory.isDatum_twistFactor | exact GlobalTheory.isDatum_twistFactor | (intros; apply GlobalTheory.isDatum_twistFactor <;> assumption)
