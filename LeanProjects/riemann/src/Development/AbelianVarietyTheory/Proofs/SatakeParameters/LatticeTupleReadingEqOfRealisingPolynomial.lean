import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealAtSuccIffDecompositionValuesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleSuccLevelPointIsComponentPointInCharStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleDecompositionOccursInFamilyStatement
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelProjection
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ExistsIsCGBases
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOne
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open Formalism.MainNotions.G.CmpJ.PStabEq

namespace GlobalTheory.TwV.DelA

theorem castSt_K_U {D : D7} {u : D.what₂.Word} {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (e : C = C') {i : ℕ} {hi : i ≤ D.R.m}
    (S : GlobalTheory.TwU.StepCharts C i hi) (c : C.cls i) :
    ((castSt e S).K ((castSt e S).chOf (castCls e i c))).lev.U = (S.K (S.chOf c)).lev.U := by
  subst e; rfl

theorem castSt_y {D : D7} {u : D.what₂.Word} {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (e : C = C') {i : ℕ} {hi : i ≤ D.R.m}
    (S : GlobalTheory.TwU.StepCharts C i hi) (c : C.cls i) :
    (castSt e S).y (castCls e i c) = S.y c := by
  subst e; rfl

set_option maxHeartbeats 2000000 in

theorem rdJ_eq_of_realAt : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (ι : ℂ →+* ℂ_[D.what₂.places.resChar w]) j (hj : j + 1 ≤ D.R.m) (h : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∀ (φ : (D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) (V : XR ((sysS H X std).Pj (j + 1)) ℂ), (∀ d : Dec J std, RealAt d (j + 1) hj h La φ V) → rdJ I X.onCh ι j La.1 La.2 φ = MvPolynomial.map ι V) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict ι j hj h La hLa φ V hR
  refine rdJ_of_isValV I X.onCh H Formalism.L2.G.RelativeIndexFlags.blockRationality_holds ι j hj La.1 La.2 hLa φ V ?_
  intro g hg c γ hγ κ hpt z z' hz
  have hcls : IsCG (I.at' j hj).st La.1 La.2 c.1 γ :=
    ⟨_, _, c.2, g, κ, (I.at' j hj).st.eC.apply_symm_apply La.1, hg, hγ, hpt⟩
  have hc0 : clsOf (H.core j hj) La.1 La.2 = c.1 := clsOf_eq (H.core j hj) hcls
  have hclsAt : clsAt X H (j + 1) La.1 La.2 = castCls (X.onCh j hj) (j + 1) c.1 := by
    rw [clsAt_succ X H j hj, hc0]
  obtain ⟨g', hg', hpt'⟩ := GlobalTheory.T.latticeTupleSuccLevel_point_isComponentPointInChart S hDict j hj La hLa
  have hx : Formalism.UG.bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ *
      (((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).y c).1 * κ.1 ∈
      UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (bc_mem hγ) (((I.at' j hj).st.K _).y c).2) (U_le κ.2)
  obtain ⟨κ₀, e₀, hχ₀⟩ := Formalism.L2.G.ptOne_of ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev
    (H.core j hj ((I.at' j hj).st.eC.symm La.1).1).int (H.core j hj ((I.at' j hj).st.eC.symm La.1).1).hypP (H.core j hj ((I.at' j hj).st.eC.symm La.1).1).bad_p ((I.at' j hj).st.eC.symm La.1).2 La.2 g g' ⟨_, hx⟩
    (J.pt std (j + 1) hj La) hg hg' hpt hpt'
  have hU : ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.U =
      ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.U := by
    unfold Joint.chart
    rw [hclsAt, J.st j hj, castSt_K_U]
    exact congrArg (fun β => ((I.at' j hj).st.K β).lev.U) c.2
  have hy : ((J.St (j + 1) hj).y (clsAt X H (j + 1) La.1 La.2)).1 =
      (((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).y c).1 := by
    rw [hclsAt, J.st j hj, castSt_y]
    exact congrArg Subtype.val ((GlobalTheory.TwU.StepCharts.ofStepIn (I.at' j hj).st).y_eq c).symm
  let κ' : ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.U := ⟨(κ * κ₀).1, by rw [hU]; exact (κ * κ₀).2⟩
  obtain ⟨d, hdγ, hdκ⟩ := GlobalTheory.T.latticeTupleDecomposition_occurs_in_family S hDict j hj La hLa γ hγ κ' (by
    rw [e₀, hy]
    show _ = _ * _ * (κ.1 * κ₀.1)
    simp only [mul_assoc])
  obtain ⟨c₂, κ₂, hc₂, hκ₂, -, hiff⟩ := GlobalTheory.T.realAt_succ_iff_decomposition_values S d j hj h La hLa
  have ec : c₂ = c := Subtype.ext (castCls_inj (X.onCh j hj) (j + 1) (hc₂.trans hclsAt))
  have eκ : κ₂ = κ * κ₀ := Subtype.ext (hκ₂.trans (by rw [hdκ]))
  have key := (hiff φ V).1 (hR d) z z' (by rw [hdγ]; exact hz)
  rw [key, ec, eκ, map_mul, Units.val_mul, hχ₀, mul_one]

end GlobalTheory.TwV.DelA

end
