import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDatumTransformUnderUnipotent
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
theorem _root_.GlobalTheory.T.flat_datum_transform_under_unipotent : ∀ (g : ℕ) (γ : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.Sp g) (M : Submodule ℤ (Fl g)), IsLat M → latAct M γ ≤ stdLat g → ∀ (j : Fl g → Pt (symMat g) g → ℂ) (m : Pt (symMat g) g → ℝ), IsDatum (siegel g) tauU (stdLat g) j m → ChernIsFlat (siegel g) tauU m → IsDatum (siegel g) tauU M (fun l P => j (l ᵥ* (γ⁻¹).mat) (actU γ P)) (fun P => m (actU γ P)) ∧ ChernIsFlat (siegel g) tauU (fun P => m (actU γ P)) := by
  first | exact @GlobalTheory.SympDatum.datum_actU | exact GlobalTheory.SympDatum.datum_actU | (intros; apply GlobalTheory.SympDatum.datum_actU <;> assumption)
