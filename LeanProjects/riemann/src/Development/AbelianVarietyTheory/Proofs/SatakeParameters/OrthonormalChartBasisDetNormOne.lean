import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteChartBasisOrthonormalLevelIndependent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalSpaceGramTransformStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem castSt_lb {D : D7} {u : D.what₂.Word} {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (h : C = C') {i : ℕ} {hi : i ≤ D.R.m}
    (S : GlobalTheory.TwU.StepCharts C i hi) (β : S.Ch) (T : GlobalTheory.TwU.StepCharts C' i hi) (hT : T = castSt h S) :
    ∃ β' : T.Ch, (T.K β').lev.Lb = (S.K β).lev.Lb := by
  subst hT
  subst h
  exact ⟨β, rfl⟩

theorem uB_det_unit : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j (hj : j ≤ D.R.m) (a : Lv.comp j) τ, ‖ι (embT D τ (uB J j hj a).1.det)‖ = 1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hPos ι hι j hj a τ
  have hU := GlobalTheory.T.local_space_gram_transform S hPos ι hι j hj
  have hO := (bAt_orth_lev S j hj a).1
  have e : (uB J j hj a).1.det = (J.A.crd j hj).1.det * (bAt J j hj a).1.det := by
    simp [uB, Matrix.det_mul]
  rw [e]
  cases j with
  | zero =>
    obtain ⟨c⟩ := Formalism.MainNotions.G.KAat.cl_nonempty J.one a
    refine hU ((J.St 0 hj).chOf (J.e0 c)) (bAt J 0 hj a) hO (fun v => ?_) τ
    rw [(J.lev0 _).1]
    exact J.lb0 v
  | succ j =>
    obtain ⟨β, hβ⟩ := castSt_lb (X.onCh j hj) (GlobalTheory.TwU.StepCharts.ofStepIn (I.at' j hj).st) ((I.at' j hj).st.eC.symm a).1 _ (J.st j hj)
    refine hU β (bAt J (j + 1) hj a) hO (fun v => ?_) τ
    rw [hβ]
    have h1 := J.lbB j hj ((I.at' j hj).st.eC.symm a).1 v
    rw [J.iw j hj _ v] at h1
    exact h1

end GlobalTheory.TwV.DelA
