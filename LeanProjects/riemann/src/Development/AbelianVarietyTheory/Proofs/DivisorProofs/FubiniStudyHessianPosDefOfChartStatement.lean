import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyHessianPosDefOfChart
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernRealClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar hermMat eval₂ bas relCot dRel IsRelAcyclic)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder
open GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernTop GlobalTheory.Points
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fubiniStudy_hessian_posDef_of_chart : ∀ (k : Type) [CommRing k] (N : ℕ) (σ : k →+* ℂ) (c0 : AlgChart (PSpace.str k N) σ N) (z : CxPts (PSpace.str k N) σ), z ∈ c0.e.source → ∀ (b : (ProjSpace.hermitianTwistingSheaf k N).B.ι), z ∈ ptsIn (PSpace.str k N) σ ((ProjSpace.hermitianTwistingSheaf k N).B.U b) → (c0.hess ((ProjSpace.hermitianTwistingSheaf k N).φ σ) b z).PosDef := by
  first | exact @GlobalTheory.FubiniStudyChart.fubiniStudy_hessian_posDef | exact GlobalTheory.FubiniStudyChart.fubiniStudy_hessian_posDef | (intros; apply GlobalTheory.FubiniStudyChart.fubiniStudy_hessian_posDef <;> assumption)
