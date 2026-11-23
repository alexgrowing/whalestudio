import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelTaylorSeriesPreservedDivisionLatticeChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnLocalDataTransportDivision
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelTaylorSeries_preserved_divisionLatticeChange : ∀ {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) (t : ColT w Z) (Y : DivX (w.D Z)) (Gy : G.LatInst (w.D Z)) (ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy) (k : KerT t Y Gy ker) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ), EntC k → ∃ k' : KerT (DivTr.colTTr w Z N h t) (divTr (D := w.D Z) N h Y) (latTr (D := w.D Z) N h Gy) (kerTr w Z N h ker), EntC k' := by
  first | exact @GlobalTheory.Mem.Top.Bl.WitTr.kerT_entC_setDiv | exact GlobalTheory.Mem.Top.Bl.WitTr.kerT_entC_setDiv | (intros; apply GlobalTheory.Mem.Top.Bl.WitTr.kerT_entC_setDiv <;> assumption)
