import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

namespace GlobalTheory.HeightCounting.Fin3

theorem emtTheta_L {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} {x : St P} (L : LocAll (lay0 (Dof x))) (l : LC hL x) {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0)
    (hY : YRel L Y) : EMtTheta Y (ysL L l) (chD L l) := by
  intro v i hv y hy n a f h
  have h2 := HEq.trans (heq_of_eq h) (hY.eW i _)
  exact (by with_unfolding_all exact ((l.c.th ((by with_unfolding_all exact (v :))) ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (hv :))) ((by with_unfolding_all exact (y :))) ((by with_unfolding_all exact (hy :))) n ((by with_unfolding_all exact (a :))) ((by with_unfolding_all exact (f :))) ((by with_unfolding_all exact ((eq_of_heq h2) :)))) :))

end GlobalTheory.HeightCounting.Fin3

end
