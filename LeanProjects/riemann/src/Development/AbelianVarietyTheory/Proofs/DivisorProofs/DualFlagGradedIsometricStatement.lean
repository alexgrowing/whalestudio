import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualFlagGradedIsometric
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnSeqShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar hermMat eval₂ bas relCot dRel IsRelAcyclic)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_flag_graded_isometric : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (E : X.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf) (fl : Vert.Flag E r) (i : Fin r), (VMetric.grLB fl i.rev H).dual.Isometric (VMetric.grLB (GlobalTheory.DualFlag.dualFlag fl) i H.dual) := by
  first | exact @GlobalTheory.VMetric.isometric_dual_grLB_rev | exact GlobalTheory.VMetric.isometric_dual_grLB_rev | (intros; apply GlobalTheory.VMetric.isometric_dual_grLB_rev <;> assumption)
