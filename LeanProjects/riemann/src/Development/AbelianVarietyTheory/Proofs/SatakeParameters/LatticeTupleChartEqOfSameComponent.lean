import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc

set_option maxHeartbeats 4000000 in

theorem chart_eq_of_comp : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m) (c : (sysS H X std).Lv.comp j) (La Lb : ((sysS H X std).Pj j).Tup), ((sysS H X std).Pj j).IsLatTup La → ((sysS H X std).Pj j).IsLatTup Lb → J.chart std j hj (c, La) = J.chart std j hj (c, Lb)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _ _ j hj c La Lb hLa hLb
  unfold Joint.chart
  rcases j with _ | j
  · haveI := J.ch0
    exact Subsingleton.elim _ _
  · simp only
    rw [Formalism.MainNotions.G.KAat.clsAt_succ X H j hj c La, Formalism.MainNotions.G.KAat.clsAt_succ X H j hj c Lb]
    have ea := Formalism.MainNotions.G.KAat.clsOf_chart (S := (I.at' j hj).st) (H.core j hj) c La hLa
    have eb := Formalism.MainNotions.G.KAat.clsOf_chart (S := (I.at' j hj).st) (H.core j hj) c Lb hLb
    have key : ∀ (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (h : (I.at' j hj).C = C) (St' : GlobalTheory.TwU.StepCharts C (j + 1) hj)
        (_ : St' = castSt h (GlobalTheory.TwU.StepCharts.ofStepIn (I.at' j hj).st)) (x y : (I.at' j hj).C.cls (j + 1)),
        (I.at' j hj).st.chOf x = (I.at' j hj).st.chOf y →
        St'.chOf (Formalism.MainNotions.G.KAat.castCls h (j + 1) x) = St'.chOf (Formalism.MainNotions.G.KAat.castCls h (j + 1) y) := by
      intro C h St' hst x y e
      subst h
      subst hst
      exact e
    exact key _ (X.onCh j hj) _ (J.st j hj) _ _ (ea.trans eb.symm)

end GlobalTheory.TwV.Xc
