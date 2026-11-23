import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RelabelledWeight

noncomputable section

namespace GlobalTheory.Mem.SRe

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.MainNotions Formalism.L2.Forms NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Top.Bl

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000 in

theorem ep_eq_reL {B : Base} {C : Cols B} (a : Late B C) (Z : New a.D) {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type}
    {A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
    (R : RealDat a.D A Ks) (F : Face a.D A) :
    EP R F = (by with_unfolding_all exact ((letI := alg (reL a Z) iK; EP (real (reL a Z) R) (face (reL a Z) F)) :)) := (congrFun (eeat_eq (reL a Z) R) (R.levR F true))

set_option maxHeartbeats 4000000 in

theorem mvEv_holds : MvEv := by
  intro B C a Z G' _ _ Pl0 T A Ks _ _ iK R F X h G t c hj
  exact (by with_unfolding_all exact ((cast (congrArg (fun E : Submodule ℂ (MMap (MP R)) =>
    EvalTieT (MP R) R.ν0 R.fd0 E X G (iotaX X h).toMulEquiv t c) (ep_eq_reL a Z R F)) hj) :))

end GlobalTheory.Mem.SRe

end
