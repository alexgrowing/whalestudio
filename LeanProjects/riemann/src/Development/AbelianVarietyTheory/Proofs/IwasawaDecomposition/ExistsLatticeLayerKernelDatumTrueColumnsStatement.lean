import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeLayerKernelDatumTrueColumns
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalRingCardinality.SpanPowerMembership.TwCore
import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Df NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latticeLayer_kernelDatum_trueColumns : StepW Pinned fun K B f T w => ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)), V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp → ∃ (Gy : G.LatInst (w.D Z)) (ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy), GyLay K (w.D Z) t.Gt t.cmp Gy ∧ ∃ kt : KerT t.toColT Y Gy ker, ∃ (Pl : Examples₂.EntPl (w.D Z)) (Bs : Formalism.L2.Ker.PlaceMatrixFamily (w.D Z)) (h : Formalism.L2.Ker.KerEntHyp Pl kt.O Bs Y (w.tw Z)), kt.E = Formalism.L2.Ker.kerEntC Pl kt.O Bs h := by
  first | exact @GlobalTheory.Mem.Top.Bl.gyLay_kerT_entC | exact GlobalTheory.Mem.Top.Bl.gyLay_kerT_entC | (intros; apply GlobalTheory.Mem.Top.Bl.gyLay_kerT_entC <;> assumption)
