import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelGroupReferenceTuple
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSingle
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_group_reference_tuple : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → ∀ (u : (q.w.D q.Z).what₂.Word) (t : (packB b).P.T), (packB b).P.I.tup t = (q.w.D q.Z).what₂.mu0 → LevG ((packB b).R.T.cols.forms u).clsP.toG 1 (levS _ (pk (packB b)).βX (datXP (pk (packB b)) (lvP (packB b)) t)) (levChi _ (pk (packB b)).βX (datXP (pk (packB b)) (lvP (packB b)) t)) := by
  first | exact @GlobalTheory.Fam.BaseLevel.levG_base_of_bWit | exact GlobalTheory.Fam.BaseLevel.levG_base_of_bWit | (intros; apply GlobalTheory.Fam.BaseLevel.levG_base_of_bWit <;> assumption)
