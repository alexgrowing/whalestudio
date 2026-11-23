import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopValueVanishingUniform
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSingle
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_value_vanishing_uniform : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → ∀ (t : (packB b).P.T) (φ : GlobalTheory.TopVal.Frm q.w.I ((packB b).P.I.tup t)) (x : (packB b).P.A3.A.fam.amb.FR t), GlobalTheory.TopVal.IsRes φ x → (∀ g y, GlobalTheory.Core.Rk.Top.HasMat g y → GlobalTheory.TopVal.IsUni q.B y → GlobalTheory.TopVal.pkAt (I := q.w.I) (l := q.w.l) (Z := q.Z) (packB b) t x g = 0) → ∀ d, GlobalTheory.TopVal.val φ d = 0 := by
  first | exact @GlobalTheory.TopVal.Inj.val_eq_zero | exact GlobalTheory.TopVal.Inj.val_eq_zero | (intros; apply GlobalTheory.TopVal.Inj.val_eq_zero <;> assumption)
