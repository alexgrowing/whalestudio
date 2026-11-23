import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.CountT
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsPos

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.ThmSOwn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (C0 : ℝ)

def kloostermanDiagonalThreshold (hC : Formalism.L2.SG.RowsPos.KppDiagP) (l : List ℝ) : ℝ :=
  max 3 (max (hC (l.getD 6 0 + 1) (1 / 4) 3 (1 / 2) (l.getD 13 0) C0 (by norm_num) (by norm_num)).choose
    (hC (l.getD 6 0 + 1) (1 / 4) 3 (1 / 2) (l.getD 13 0) C0 (by norm_num) (by norm_num)).choose_spec.choose)

theorem hypOwnE_kppDiagP (hC : Formalism.L2.SG.RowsPos.KppDiagP) (hAbs : Formalism.L2.SG.RowsConc.AbsConvTied) {𝒞 : FamClass}
    (hE : Closed 𝒞 fun Fm _ => ConcEv C0 Fm) :
    Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D _ => ClKppDiag D := by
  refine closed_with hE (fun _ => 0) (kloostermanDiagonalThreshold C0 hC) fun Fm CH _ hE' _ h1 h2 => ?_
  obtain ⟨x0, H⟩ := hE'
  refine ⟨x0, fun x hx i hH => ?_⟩
  obtain ⟨c⟩ := H x hx i hH
  have hs := (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 (by norm_num) (by norm_num)).choose_spec.choose_spec
  have e : kloostermanDiagonalThreshold C0 hC (Fm.cOut ++ Fm.cMid CH) = max 3 (max (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0
      (by norm_num) (by norm_num)).choose
      (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 (by norm_num) (by norm_num)).choose_spec.choose) := rfl
  rw [e] at h1 h2
  have hC' : 1 ≤ sC' Fm := le_trans (by norm_num) (le_trans (le_max_left _ _) h1)
  have hK2 := Formalism.MainNotions.NonGenericAndKTwoTheorems.Hyp_of _ _ _ _ _ _ _ _ _ _ hH.1 hH.2.1 hH.2.2 hC'
  intro u
  have hA := hAbs _ c.X c.Y u u c.tie
  have hd := (hs _ _ (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) h1))
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) h2)) _ _ c.X c.Y u (Fm.ties x i) hK2 c.tie hA).2
  unfold Formalism.L2.SG.RowsOther.KppDiag at hd
  rw [c.tie.2.2.1 u] at hd
  rw [hsNormSq_Kpp c.hI hA]
  unfold AdmissibleBoundsFromSource.du AdmissibleBoundsFromSource.xK
  exact hd

def cDiagLP (hC : Formalism.L2.SG.RowsPos.DiagLP) (l : List ℝ) :=
  hC (l.getD 6 0 + 1) (1 / 4) 3 (1 / 2) (l.getD 13 0) C0 1 (by norm_num) (by norm_num)

def thmDLP (hC : Formalism.L2.SG.RowsPos.DiagLP) (l : List ℝ) : ℝ :=
  max (cDiagLP C0 hC l).choose (cDiagLP C0 hC l).choose_spec.choose + 1

def thDLP (hC : Formalism.L2.SG.RowsPos.DiagLP) (l : List ℝ) : ℝ :=
  if h : thmDLP C0 hC (l.take 16) ≤ l.getD 17 0 then
    max 3 (max ((cDiagLP C0 hC (l.take 16)).choose_spec.choose_spec.2.2 (l.getD 17 0) h).choose
      ((cDiagLP C0 hC (l.take 16)).choose_spec.choose_spec.2.2 (l.getD 17 0) h).choose_spec.choose)
  else 3

theorem hypOwnL_diagP (hC : Formalism.L2.SG.RowsPos.DiagLP) (hExp : KExpTied) (hAbs : Formalism.L2.SG.RowsConc.AbsConvTied)
    {𝒞 : FamClass} (sel : SSel 𝒞)
    (hOK : Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, SelOK C0 Fm (sel Fm hc)) (hLp : LoopRowS C0 𝒞 sel) :
    Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D _ => ClDiag D := by
  refine closed_with (hOK.and (hLp fun _ => 1)) (thmDLP C0 hC) (thDLP C0 hC) fun Fm CH hc hQ hm h1 h2 => ?_
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
  have hm' : thmDLP C0 hC ((Fm.cOut ++ Fm.cMid CH).take 16) ≤ (Fm.cOut ++ Fm.cMid CH).getD 17 0 := by
    rw [e0, e17]; exact hm
  have e1 : thDLP C0 hC (Fm.cOut ++ Fm.cMid CH) = max 3
      (max ((cDiagLP C0 hC ((Fm.cOut ++ Fm.cMid CH).take 16)).choose_spec.choose_spec.2.2 _ hm').choose
        ((cDiagLP C0 hC ((Fm.cOut ++ Fm.cMid CH).take 16)).choose_spec.choose_spec.2.2 _ hm').choose_spec.choose) :=
    dif_pos hm'
  have hs := ((cDiagLP C0 hC ((Fm.cOut ++ Fm.cMid CH).take 16)).choose_spec.choose_spec.2.2 _ hm').choose_spec.choose_spec
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
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) h2)) _ _ c.X c.Y u (Fm.ties x i) hH5 hK2.2 c.tie hA hG hRB hRNS
  unfold Formalism.L2.SG.RowsOther.DiagRow Formalism.L2.SG.RowsConc.ddC at hd
  rw [c.tie.2.2.1 u, c.tie.2.2.2.1, (Fm.D x i).GamP_eq u] at hd
  rw [hsNormSq_diag c.hI (hExp _ c.X c.Y u u c.tie) hA (Formalism.L2.SG.Pf.SatGram.idDegenerate_tO c.Y u u)]
  unfold AdmissibleBoundsFromSource.Gam AdmissibleBoundsFromSource.du AdmissibleBoundsFromSource.Dst
  calc _ ≤ _ := hd
    _ = _ := by ring

theorem theoremS_link_of_evaluation (P : ∀ I : AutInst, Measure I.Gf → ℕ → (I.Gf → ℂ) → Prop) {eps : ℝ} (Fm : FamP eps)
    (Cg cb Cu cT CT C0 : ℝ) (n0 : ℕ) (A C c7 cb7 : ℝ) (h1 : 1 ≤ C0) (hC : 0 ≤ C)
    (hA : 2 * Cg ≤ A) (hCl2 : 2 ≤ sCl Fm) (hCl3 : 2 * C ≤ sCl Fm)
    (hS0 : StandingHypothesesWithConstants Fm Cg cb Cu cT CT C0)
    (hR : ∃ xR : ℝ, ∀ x ≥ xR, Fm.x1 < x → ∀ i : Fm.Ix x, ∃ X : RowsAut, CountE.RowsTieP P (Fm.D x i) X)
    (hT : Formalism.MainNotions.S.ThmSOwn Fm Cg cb Cu cT CT C0) (h30 : CountE.CountAllPointsClass P Fm n0 A C c7 cb7) : Formalism.MainNotions.LinkS Fm C0 := by
  have h30R : CountE.CountRowsClassFamily P Fm n0 A C c7 cb7 :=
    ⟨h30.1, h30.2.1, fun x i => CountE.count_rows_class_of_count_class P n0 A C c7 cb7 (h30.2.2 x i)⟩
  exact linkS_of_standing_hypotheses Fm Cg cb Cu cT CT C0 c7 h1 h30.1 hS0 hT
    (countOwn_of_rowsPEv P Fm Cg cb Cu cT CT C0 n0 A C c7 cb7 hC hA hCl2 hCl3 hR h30R)

theorem theoremS_link_concrete (P : ∀ I : AutInst, Measure I.Gf → ℕ → (I.Gf → ℂ) → Prop)
    (𝒞 : FamClass) (C0 : ℝ) (c30 : List ℝ → CountingConstants) (h1 : 1 ≤ C0)
    (hc30 : ∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A)
    (hRes : Closed 𝒞 fun Fm _ => ResidEv Fm)
    (hRows : Closed 𝒞 fun Fm _ => ∃ xR : ℝ, ∀ x ≥ xR, Fm.x1 < x → ∀ i : Fm.Ix x, ∃ X : RowsAut,
      CountE.RowsTieP P (Fm.D x i) X)
    (hK1 : Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D _ => ClKppOff D)
    (hK2 : Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D _ => ClKppDiag D)
    (hK3 : Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D L => ClOff D L)
    (hK4 : Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D _ => ClDiag D)
    (h30 : Closed 𝒞 fun Fm _ => CountE.CountAllPointsClass P Fm (c30 Fm.cOut).n0 (c30 Fm.cOut).A (c30 Fm.cOut).C
      (c30 Fm.cOut).c (c30 Fm.cOut).cb) :
    Closed 𝒞 fun Fm _ => TuSize Fm → Formalism.MainNotions.LinkS Fm C0 :=
  closed_of_large (linkThresholds (fun _ => caZero) c30)
    (hRes.and (hRows.and (hK1.and (hK2.and (hK3.and (hK4.and h30))))))
    fun Fm CH hL h a0 => by
      obtain ⟨-, g2, g3, g4⟩ := link_thresholds_spec Fm CH (fun _ => caZero) c30 hL
      obtain ⟨a1, a2, k1, k2, k3, k4, a6⟩ := h
      exact theoremS_link_of_evaluation P Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 _ _ _ _ _ h1
        (hc30 Fm).1 (hc30 Fm).2 g2 g3 (standing_hypotheses_hold_family Fm C0 h1 ⟨g4, a0, a1⟩) a2 (thmSOwn_of_clauses k1 k2 k3 k4) a6

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

theorem theoremS_transport_link_zero (𝒞 : FamClass) (sel : SSel 𝒞)
    (hWu : Formalism.L2.SG.Pf.WuDecayOfGap) (hRF : Formalism.L2.SG.RowsDef.RowsFinDim)
    (hLoc : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : Fm.x1 < x) (h0 : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.SG.Pf.LocCP.LocTied (Fm.D x i))
    (hInst : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : Fm.x1 < x) (h0 : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      InstTie ((sel Fm hc).2 x hx h0 i).X.B.I)
    (hQ : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : Fm.x1 < x) (h0 : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      1 ≤ qqI ((sel Fm hc).2 x hx h0 i).X.B.I)
    (hTF : Closed 𝒞 fun Fm _ => PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0)
    (c30 : List ℝ → CountingConstants) (h1 : 1 ≤ C0)
    (hc30 : ∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A)
    (hRes : Closed 𝒞 fun Fm _ => ResidEv Fm)
    (hTy : Formalism.L2.SG.RowsPos.TypeP) (hNG : Formalism.L2.SG.RowsPos.RowNGP) (hM : Formalism.L2.SG.RowsPos.RowMainEqP)
    (hLp : LoopRowS C0 𝒞 sel)
    (hO : Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, TheoremSSelected Fm C0 (sel Fm hc))
    (h30 : Closed 𝒞 fun Fm _ => CountE.CountAllPointsClass PLevT' Fm (c30 Fm.cOut).n0 (c30 Fm.cOut).A (c30 Fm.cOut).C
      (c30 Fm.cOut).c (c30 Fm.cOut).cb) :
    Closed 𝒞 fun Fm _ => TuSize Fm → Formalism.MainNotions.LinkS Fm C0 :=
  have hFX := Formalism.L2.SG.Pf.finXC_of hWu hRF
  have hOK := selOK_of C0 hFX hWu sel hLoc hTF
  have hE : Closed 𝒞 fun Fm _ => ConcEv C0 Fm :=
    closed_with hOK (fun _ => 0) (fun _ => 0) fun Fm _ hc h _ _ _ => concEv_of_sel C0 (h hc)
  have hRows : Closed 𝒞 fun Fm _ => ∃ xR : ℝ, ∀ x ≥ xR, Fm.x1 < x → ∀ i : Fm.Ix x, ∃ X : RowsAut,
      CountE.RowsTieP PLevT' (Fm.D x i) X :=
    closed_of_th (fun _ => 0) (fun _ => 0) fun Fm _ hc _ _ _ =>
      ⟨(sel Fm hc).1, fun x hx0 hx i =>
        ⟨_, rowsTiePT'_of ((sel Fm hc).2 x hx hx0 i) (hInst Fm hc x hx hx0 i) (hQ Fm hc x hx hx0 i)⟩⟩
  theoremS_link_concrete PLevT' 𝒞 C0 c30 h1 hc30 hRes hRows (hypOwnE_kppOff C0 Formalism.L2.SG.Closed.KppOffC_holds hE)
    (hypOwnE_kppDiagP C0 (Formalism.L2.SG.RowsPos.kernel_diagonal_positive hTy) absConvTied_holds hE)
    (hypOwnS_off C0 Formalism.L2.SG.Closed.KppOffC_holds kExpTied_holds absConvTied_holds sel hOK hO)
    (hypOwnL_diagP C0 (Formalism.L2.SG.RowsPos.diagonal_positive_final hNG hM) kExpTied_holds absConvTied_holds sel hOK hLp) h30

end Formalism.L2.SG.ThmSOwn
