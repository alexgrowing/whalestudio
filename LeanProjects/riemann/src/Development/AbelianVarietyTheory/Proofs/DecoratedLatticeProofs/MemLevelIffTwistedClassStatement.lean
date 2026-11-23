import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevelIffTwistedClass
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSingle
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_level_iff_twisted_class : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → ∀ (u : (q.w.D q.Z).what₂.Word) (t : (packB b).P.T) (h : (packB b).P.I.tup t ≠ (q.w.D q.Z).what₂.mu0) (g : GA (q.w.D q.Z) (q.w.D q.Z).sp.X'), g ∈ (levS _ (pk (packB b)).βX (datXP (pk (packB b)) (lvP (packB b)) t)) ↔ ∃ κ : ((packB b).R.T.tw.pt.cls u ((packB b).P.I.tup t) h).lev.U, GlobalTheory.Core.Rk.Top.HasMat g κ.1 := by
  first | exact @GlobalTheory.TopVal.TwSet.levS_iff_cls | exact GlobalTheory.TopVal.TwSet.levS_iff_cls | (intros; apply GlobalTheory.TopVal.TwSet.levS_iff_cls <;> assumption)
