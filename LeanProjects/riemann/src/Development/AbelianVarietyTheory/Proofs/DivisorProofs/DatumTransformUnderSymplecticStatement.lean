import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumTransformUnderSymplectic
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
theorem _root_.GlobalTheory.T.datum_transform_under_symplectic : ∀ (g : ℕ) (γ : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.Sp g) (L : Submodule ℤ (Fl g)), IsLat L → L ≤ stdLat g → ∀ (j : Fl g → Pt (symMat g) g → ℂ) (m : Pt (symMat g) g → ℝ), IsDatum (siegel g) tauU (stdLat g) j m → IsDatum (siegel g) (fun s => moeb γ (tauU s)) L (fun l P => j l (actB γ P.1, P.2)) (fun P => m (actB γ P.1, P.2)) := by
  first | exact @GlobalTheory.ThetaPull.isDatum_pull | exact GlobalTheory.ThetaPull.isDatum_pull | (intros; apply GlobalTheory.ThetaPull.isDatum_pull <;> assumption)
