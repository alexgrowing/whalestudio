import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConcreteSplitPrimeAutomorphicDataDivisionLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnLocalDataTransportDivision
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.concreteSplitPrimeAutomorphicData_divisionLatticeChange : ∀ (sc : Scale) (D : D7) (Gt : GatTies D) (c : LatCmp D) (H : Formalism.L2.Herm.Herm0 D) (F : ∀ u, Formalism.L2.Forms.Forms0 D u) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ), IsRecG sc D Gt c H F → IsRecG sc (setDiv D N h) (gatTr N h Gt) (cmpTr N h c) (DivTr.herm0S N h H) (fun u => DivTr.forms0S N h (F u)) := by
  first | exact @GlobalTheory.Mem.Top.Bl.WitTr.isRecG_setDiv | exact GlobalTheory.Mem.Top.Bl.WitTr.isRecG_setDiv | (intros; apply GlobalTheory.Mem.Top.Bl.WitTr.isRecG_setDiv <;> assumption)
