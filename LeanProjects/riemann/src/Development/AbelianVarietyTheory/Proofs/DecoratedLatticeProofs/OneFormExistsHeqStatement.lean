import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneFormExistsHeq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSingle
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_form_exists_heq : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → Nonempty (Bl.RXs q.x.what₂) → ∀ (t : (packB b).P.T) (F : Fin (((packB b).P.A3.side3 (packB b).P.Ps (packB b).P.ψs (packB b).P.Zs).nV t) → (q.w.D q.Z).what₂.LL) (F' : Fin (((packB b).Q.F.fc (cxW (packB b)).zs).Df1.nV t) → (q.w.D q.Z).what₂.LL), HEq F F' → ∃ φ : GlobalTheory.TopVal.Frm q.w.I ((packB b).P.I.tup t), GlobalTheory.TopVal.IsRes φ ((packB b).Q.F.eV (cxW (packB b)).zs t F') ∧ ∀ u, GlobalTheory.TopVal.RecVal (I := q.w.I) (l := q.w.l) (Z := q.Z) u ((packB b).P.I.tup t) φ ((packB b).P.I.jA t ((rV0 (q.w.D q.Z) (packB b).P.A3.A (packB b).P.Ps (packB b).P.ψs t).mulVec F)) := by
  first | exact @GlobalTheory.TopVal.OneForm.recVal_packB | exact GlobalTheory.TopVal.OneForm.recVal_packB | (intros; apply GlobalTheory.TopVal.OneForm.recVal_packB <;> assumption)
