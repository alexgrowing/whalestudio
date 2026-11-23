import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualFlagBottChernSum
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
theorem _root_.GlobalTheory.T.dual_flag_bott_chern_sum : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X] (E : X.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf) (fl : Vert.Flag E r) (σ : k →+* ℂ), IsRegSurf p → ∑ i, ((h.dual.stepMet (GlobalTheory.DualFlag.dualFlag fl) i).met σ).bcMeas (VMetric.stepSeq_shortExact (GlobalTheory.DualFlag.dualFlag fl) i) ((GlobalTheory.DualFlag.dualFlag fl).isVB i.castSucc) ((GlobalTheory.DualFlag.dualFlag fl).isVB_gr i) univ = ∑ i, ((h.stepMet fl i).met σ).bcMeas (VMetric.stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i) univ := by
  first | exact @GlobalTheory.DualFlagBc.sum_bcMeas_dualFlag | exact GlobalTheory.DualFlagBc.sum_bcMeas_dualFlag | (intros; apply GlobalTheory.DualFlagBc.sum_bcMeas_dualFlag <;> assumption)
