import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetUnitaryAdelicPointGramStepNormOne
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV

theorem castSt_y_castCls {D : D7} {u : D.what₂.Word} {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (h : C = C') {i : ℕ} {hi : i ≤ D.R.m}
    (S : GlobalTheory.TwU.StepCharts C i hi) (c : C.cls i) : (castSt h S).y (castCls h i c) = S.y c := by
  subst h; rfl

theorem exists_isDetOf_uPts (D : D7) (i : ℕ) (hi : i ≤ D.R.m)
    (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Formalism.L2.Herm.IsDetOf D.sp.cm y x.1 := by
  have hd := det_unitary_adelic_point_gram_step_norm_one D i hi x
  refine ⟨⟨Units.map (Matrix.scalar (Fin 1)).toMonoidHom (Matrix.GeneralLinearGroup.det x.1), ?_⟩, ?_⟩
  · simp only [Formalism.L2.DIV.U1, MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.id_apply, Formalism.L2.DIV.conjId] at hd
    have hd' := congrArg Units.val hd
    simp only [Units.val_mul, Units.coe_map, Units.val_one, MonoidHom.coe_coe] at hd'
    show cT _ _ * _ * _ = _
    ext a b
    fin_cases a; fin_cases b
    simp [cT, Matrix.mul_apply, Matrix.scalar_apply, inclE]
    rw [← Algebra.TensorProduct.one_def, mul_one, mul_comm]
    exact hd'
  · ext
    simp [Formalism.L2.Herm.IsDetOf, Matrix.GeneralLinearGroup.det]

theorem tw_at_rep : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j + 1 ≤ D.R.m) (β : (I.at' j hj).st.Ch) (c : {c // (I.at' j hj).st.chOf c = β}), ((I.at' j hj).st.tw β).ch (((I.at' j hj).st.K β).y c) = D.chiD ((t.O u μ).dt (j + 1) (castCls (X.onCh j hj) (j + 1) c.1)) ^ cTw D (j + 1)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S j hj β c
  obtain ⟨y, hy⟩ := exists_isDetOf_uPts D (j + 1) hj (((I.at' j hj).st.K β).y c)
  rw [J.tw j hj β _ y hy]
  have hrep : (J.St (j + 1) hj).y (castCls (X.onCh j hj) (j + 1) c.1) = ((I.at' j hj).st.K β).y c := by
    have e := J.st j hj
    revert e
    generalize J.St (j + 1) hj = St'
    intro e
    subst e
    rw [castSt_y_castCls]
    exact (GlobalTheory.TwU.StepCharts.y_eq (GlobalTheory.TwU.StepCharts.ofStepIn (I.at' j hj).st) c).symm
  rw [J.tie.dt (j + 1) hj _ y (by rw [hy, hrep])]

end GlobalTheory.TwV
