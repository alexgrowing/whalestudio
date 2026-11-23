import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTwistsThetaLatticesPreservedDivisionChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnLocalDataTransportDivision
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodTwistsThetaLattices_preserved_divisionChange : ∀ (D : D7) (nch : NChoice D) (xd : ThData D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ), GoodO D nch xd → GoodO (setDiv D N h) (nchTr N h nch) (xdTr N h xd) := by
  first | exact @GlobalTheory.Mem.Top.Bl.WitTr.goodO_setDiv | exact GlobalTheory.Mem.Top.Bl.WitTr.goodO_setDiv | (intros; apply GlobalTheory.Mem.Top.Bl.WitTr.goodO_setDiv <;> assumption)
