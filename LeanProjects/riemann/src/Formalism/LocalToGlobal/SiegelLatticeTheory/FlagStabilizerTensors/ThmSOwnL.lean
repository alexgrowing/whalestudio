import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DiagCL

noncomputable section

open scoped Classical InnerProductSpace ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.ThmSOwn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section DiagL

open Formalism.L2.SG.Full

variable (C0 : ℝ)

def cDiagL (hC : Formalism.L2.SG.RowsConc.DiagCL) (l : List ℝ) :=
  hC (l.getD 6 0 + 1) (1 / 4) 3 (1 / 2) (l.getD 13 0) C0 1

def thmDL (hC : Formalism.L2.SG.RowsConc.DiagCL) (l : List ℝ) : ℝ :=
  max (cDiagL C0 hC l).choose (cDiagL C0 hC l).choose_spec.choose + 1

def thDL (hC : Formalism.L2.SG.RowsConc.DiagCL) (l : List ℝ) : ℝ :=
  if h : thmDL C0 hC (l.take 16) ≤ l.getD 17 0 then
    max 3 (max ((cDiagL C0 hC (l.take 16)).choose_spec.choose_spec.2.2 (l.getD 17 0) h).choose
      ((cDiagL C0 hC (l.take 16)).choose_spec.choose_spec.2.2 (l.getD 17 0) h).choose_spec.choose)
  else 3

theorem closed_clDiag_of_selOK (hC : Formalism.L2.SG.RowsConc.DiagCL) (hExp : KExpTied) (hAbs : Formalism.L2.SG.RowsConc.AbsConvTied)
    {𝒞 : FamClass} (sel : SSel 𝒞)
    (hOK : Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, SelOK C0 Fm (sel Fm hc)) (hLp : LoopRowS C0 𝒞 sel) :
    Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D _ => ClDiag D := by
  refine closed_with (hOK.and (hLp fun _ => 1)) (thmDL C0 hC) (thDL C0 hC) fun Fm CH hc hQ hm h1 h2 => ?_
  obtain ⟨x2, H2⟩ := hQ.1 hc
  obtain ⟨x3, H3⟩ := hQ.2 hc
  refine ⟨max x2 (max x3 (max (sel Fm hc).1 (Fm.x1 + 1))), fun x hx i hH => ?_⟩
  have hxa := le_trans (le_max_right _ _) hx
  have hx' := le_trans (le_max_right _ _) hxa
  have hx1 : Fm.x1 < x := by have := le_trans (le_max_right _ _) hx'; linarith
  have h0 : (sel Fm hc).1 ≤ x := le_trans (le_max_left _ _) hx'
  let c := concKOf ((sel Fm hc).2 x hx1 h0 i) (H2 x (le_trans (le_max_left _ _) hx) i hH hx1 h0)
  have e0 : (Fm.cOut ++ Fm.cMid CH).take 16 = Fm.cOut := rfl
  have e17 : (Fm.cOut ++ Fm.cMid CH).getD 17 0 = Fm.CGam := rfl
  have hm' : thmDL C0 hC ((Fm.cOut ++ Fm.cMid CH).take 16) ≤ (Fm.cOut ++ Fm.cMid CH).getD 17 0 := by
    rw [e0, e17]; exact hm
  have e1 : thDL C0 hC (Fm.cOut ++ Fm.cMid CH) = max 3
      (max ((cDiagL C0 hC ((Fm.cOut ++ Fm.cMid CH).take 16)).choose_spec.choose_spec.2.2 _ hm').choose
        ((cDiagL C0 hC ((Fm.cOut ++ Fm.cMid CH).take 16)).choose_spec.choose_spec.2.2 _ hm').choose_spec.choose) :=
    dif_pos hm'
  have hs := ((cDiagL C0 hC ((Fm.cOut ++ Fm.cMid CH).take 16)).choose_spec.choose_spec.2.2 _ hm').choose_spec.choose_spec
  rw [e1] at h1 h2
  have hC' : 1 ≤ sC' Fm := le_trans (by norm_num) (le_trans (le_max_left _ _) h1)
  have hCl : 2 < sCl Fm := lt_of_lt_of_le (by norm_num) (le_trans (le_max_left _ _) h2)
  have hK2 := Formalism.MainNotions.NonGenericAndKTwoTheorems.Hyp_of _ _ _ _ _ _ _ _ _ _ hH.1 hH.2.1 hH.2.2 hC'
  intro u
  have hH5 := Formalism.MainNotions.count_hypotheses_diagonal_words _ _ _ _ _ _ _ _ _ _ 1 hH.1 hH.2.1 hH.2.2 hCl hC' le_rfl u
  have hA := hAbs _ c.X c.Y u u c.tie
  obtain ⟨hRB, hRNS⟩ := H3 x (le_trans (le_max_left _ _) hxa) i hx1 h0 u u hH5 c.tie hA
  have hG : (Fm.L x i).CGam = (Fm.cOut ++ Fm.cMid CH).getD 17 0 := by rw [e17]; exact Fm.CGam_eq x i
  have hd := hs _ _ (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) h1))
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) h2)) _ _ c.X c.Y u hH5 hK2.2 c.tie hA hG hRB hRNS
  unfold Formalism.L2.SG.RowsOther.DiagRow Formalism.L2.SG.RowsConc.ddC at hd
  rw [c.tie.2.2.1 u, c.tie.2.2.2.1, (Fm.D x i).GamP_eq u] at hd
  rw [hsNormSq_diag c.hI (hExp _ c.X c.Y u u c.tie) hA (Formalism.L2.SG.Pf.SatGram.idDegenerate_tO c.Y u u)]
  unfold AdmissibleBoundsFromSource.Gam AdmissibleBoundsFromSource.du AdmissibleBoundsFromSource.Dst
  calc _ ≤ _ := hd
    _ = _ := by ring

end DiagL

end Formalism.L2.SG.ThmSOwn
