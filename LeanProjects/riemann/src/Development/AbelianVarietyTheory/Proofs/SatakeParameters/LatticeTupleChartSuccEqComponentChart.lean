import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000

namespace GlobalTheory.TwV.ChartSucc

theorem castSt_ofStepIn_chart {D : D7} {u : D.what₂.Word} {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (h : C = C') {i : ℕ} {hi : i ≤ D.R.m}
    {A : ColumnsAtT D.R C} {P : PeriodMap D.R C} {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}
    {p : ℕ} {G : GAtP p} (S : StepIn M i hi G) (St : GlobalTheory.TwU.StepCharts C' i hi) (hSt : St = castSt h (GlobalTheory.TwU.StepCharts.ofStepIn S))
    (c : C.cls i) (c' : C'.cls i) (hc' : c' = castCls h i c) (β : S.Ch) (hβ : S.chOf c = β) :
    St.T = S.T ∧ (St.K (St.chOf c')).lev.Lb = (S.K β).lev.Lb ∧ (St.K (St.chOf c')).lev.U = (S.K β).lev.U ∧
      (St.K (St.chOf c')).lev.Uloc = (S.K β).lev.Uloc ∧ ∀ hc : S.chOf c = β, St.y c' = (S.K β).y ⟨c, hc⟩ := by
  subst hSt hc' h hβ
  exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩

end GlobalTheory.TwV.ChartSucc

theorem GlobalTheory.TwV.chart_succ_eq : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → (I.at' j hj).st.T = (D.mem u).A.T ∧ ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.Lb = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.Lb ∧ ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.U = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.U ∧ ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.Uloc = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.Uloc ∧ ∀ hc : (I.at' j hj).st.chOf (clsOf (S := (I.at' j hj).st) (H.core j hj) La.1 La.2) = ((I.at' j hj).st.eC.symm La.1).1, (J.St (j + 1) hj).y (clsAt X H (j + 1) La.1 La.2) = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).y ⟨_, hc⟩ := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j hj La hLa
  have hc := clsOf_chart (S := (I.at' j hj).st) (H.core j hj) La.1 La.2 hLa
  obtain ⟨hT', hLb, hU, hUl, hy⟩ := GlobalTheory.TwV.ChartSucc.castSt_ofStepIn_chart (X.onCh j hj) (I.at' j hj).st (J.St (j + 1) hj) (J.st j hj)
    _ (clsAt X H (j + 1) La.1 La.2) (clsAt_succ X H j hj La.1 La.2) _ hc
  refine ⟨hT'.symm.trans (J.tie.T_eq (j + 1) hj), hLb, hU, hUl, hy⟩
