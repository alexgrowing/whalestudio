import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwnL
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FullExistsTiedHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FinXClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DiagCLC
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KloostermanDiagonalOfType

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.ThmSOwn

section Ev

open Formalism.MainNotions.S.CountE Formalism.MainNotions.PlaceDegreeData

variable (P : ∀ I : AutInst, Measure I.Gf → ℕ → (I.Gf → ℂ) → Prop) {eps : ℝ} (Fm : FamP eps)

theorem countOwn_of_rowsPEv (Cg cb Cu cT CT C0 : ℝ) (n0 : ℕ) (A C c cb7 : ℝ) (hC : 0 ≤ C) (hA : 2 * Cg ≤ A)
    (hCl2 : 2 ≤ sCl Fm) (hCl3 : 2 * C ≤ sCl Fm)
    (hR : ∃ xR : ℝ, ∀ x ≥ xR, Fm.x1 < x → ∀ i : Fm.Ix x, ∃ X : RowsAut, RowsTieP P (Fm.D x i) X)
    (h30 : CountRowsClassFamily P Fm n0 A C c cb7) : CountOwn Fm Cg cb Cu cT CT C0 c := by
  obtain ⟨xR, HR⟩ := hR
  obtain ⟨-, hcb, h30⟩ := h30
  have hG := cGam_pos Fm
  obtain ⟨Y1, hY1, HY1⟩ := linear_le_pow_eight_eventually (8 * Fm.CGam) n0 (by positivity)
  obtain ⟨Y2, -, HY2⟩ := linear_le_pow_eight_eventually (cb7 * (8 * Fm.CGam)) 8 (by positivity)
  obtain ⟨x4, hx4⟩ := ev_y Fm (max Y1 Y2)
  refine ⟨max (max (Fm.x1 + 1) x4) xR, fun x hx i hH => ?_⟩
  have hxa := le_trans (le_max_left _ _) hx
  have hx1 : Fm.x1 < x := by
    have := le_trans (le_max_left _ _) hxa
    linarith
  have hy := hx4 x (le_trans (le_max_right _ _) hxa)
  set y : ℝ := x ^ (eps / 8) with hydef
  have hy1 : 1 ≤ y := le_trans hY1 (le_trans (le_max_left _ _) hy)
  have a1 := HY1 y (le_trans (le_max_left _ _) hy)
  have a2 := HY2 y (le_trans (le_max_right _ _) hy)
  have hL := scL_eq Fm x hx1 i
  have hh : AdmissibleBoundsFromSource.hyp (Fm.D x i) (Fm.L x i) C0 (sC' Fm) (sCl Fm) Cg cb Cu cT CT := ⟨hH.2.1, hH.1, hH.2.2⟩
  have hk8 := k_ge_of_hyp (Fm.L x i) hh
  rw [hL, Fm.CGam_eq x i] at hk8
  obtain ⟨X, hX⟩ := HR x (le_trans (le_max_right _ _) hx) hx1 i
  refine admissibility_ten_of_rows_class P (Fm.L x i) X hX n0 A C cb7 c (h30 x i)
    (count_parameters_of_hyp (Fm.L x i) C0 _ _ Cg cb Cu cT CT n0 A C cb7 hC hcb hA ?_ hCl2 hCl3 ?_ hh)
  · have : (n0 : ℝ) ≤ n0 * y := le_mul_of_one_le_right (Nat.cast_nonneg _) hy1
    linarith
  · rw [hL, Real.log_pow]
    have h1 : Real.log y ≤ y := Real.log_le_self (by linarith)
    have h2 : cb7 * (8 * Fm.CGam * y ^ 8) ≤ cb7 * ((Fm.D x i).R.k : ℝ) := mul_le_mul_of_nonneg_left hk8 hcb.le
    push_cast
    nlinarith

theorem linkS_of_thmSPEv (Cg cb Cu cT CT C0 Cres : ℝ) (n0 : ℕ) (A Cb C c7 cb7 : ℝ) (h1 : 1 ≤ C0) (hC : 0 ≤ C)
    (hA : 2 * Cg ≤ A) (hCl2 : 2 ≤ sCl Fm) (hCl3 : 2 * C ≤ sCl Fm)
    (hS0 : StandingHypothesesWithConstants Fm Cg cb Cu cT CT C0)
    (hR : ∃ xR : ℝ, ∀ x ≥ xR, Fm.x1 < x → ∀ i : Fm.Ix x, ∃ X : RowsAut, RowsTieP P (Fm.D x i) X)
    (hT : ThmSOwn Fm Cg cb Cu cT CT C0)
    (S30 : ShareFamilyAtConstant P Fm Cres n0 A Cb C c7 cb7) (A30 : PlaceDegreeData.AdmF Fm Cres) : Formalism.MainNotions.LinkS Fm C0 := by
  have h30 : CountAllPointsClass P Fm n0 A C c7 cb7 := (S30 A30).2.2.2.2.2.2
  have h30R : CountRowsClassFamily P Fm n0 A C c7 cb7 :=
    ⟨h30.1, h30.2.1, fun x i => count_rows_class_of_count_class P n0 A C c7 cb7 (h30.2.2 x i)⟩
  exact linkS_of_standing_hypotheses Fm Cg cb Cu cT CT C0 c7 h1 h30.1 hS0 hT
    (countOwn_of_rowsPEv P Fm Cg cb Cu cT CT C0 n0 A C c7 cb7 hC hA hCl2 hCl3 hR h30R)

end Ev

theorem linkS_concreteEv (𝒞 : FamClass) (C0 : ℝ) (c30 : List ℝ → CountingConstants) (h1 : 1 ≤ C0)
    (hc30 : ∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A)
    (hRes : Closed 𝒞 fun Fm _ => ResidEv Fm)
    (hRows : Closed 𝒞 fun Fm _ => ∃ xR : ℝ, ∀ x ≥ xR, Fm.x1 < x → ∀ i : Fm.Ix x, ∃ X : RowsAut,
      CountE.RowsTieP CountE.PLev (Fm.D x i) X)
    (hK1 : Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D _ => ClKppOff D)
    (hK2 : Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D _ => ClKppDiag D)
    (hK3 : Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D L => ClOff D L)
    (hK4 : Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D _ => ClDiag D)
    (S30 : Closed 𝒞 fun Fm _ => CountE.ShareFamilyAtConstant CountE.PLev Fm (c30 Fm.cOut).Cres (c30 Fm.cOut).n0 (c30 Fm.cOut).A
      (c30 Fm.cOut).Cb (c30 Fm.cOut).C (c30 Fm.cOut).c (c30 Fm.cOut).cb)
    (A30 : Closed 𝒞 fun Fm _ => PlaceDegreeData.AdmF Fm (c30 Fm.cOut).Cres) :
    Closed 𝒞 fun Fm _ => TuSize Fm → Formalism.MainNotions.LinkS Fm C0 :=
  closed_of_large (linkThresholds (fun _ => caZero) c30)
    (hRes.and (hRows.and (hK1.and (hK2.and (hK3.and (hK4.and (S30.and A30)))))))
    fun Fm CH hL h a0 => by
      obtain ⟨-, g2, g3, g4⟩ := link_thresholds_spec Fm CH (fun _ => caZero) c30 hL
      obtain ⟨a1, a2, k1, k2, k3, k4, a6, a7⟩ := h
      exact linkS_of_thmSPEv CountE.PLev Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 _ _ _ _ _ _ _ h1
        (hc30 Fm).1 (hc30 Fm).2 g2 g3 (standing_hypotheses_hold_family Fm C0 h1 ⟨g4, a0, a1⟩) a2 (thmSOwn_of_clauses k1 k2 k3 k4) a6 a7

theorem kExpTied_holds : KExpTied :=
  kExpTied_of_full Formalism.L2.SG.Closed.FoldOKC_outright Formalism.L2.SG.Closed.InHHC_holds Formalism.L2.SG.Closed.FundExistsC_holds
    Formalism.L2.SG.Closed.OOIntAllC_outright Formalism.L2.SG.Closed.OOFundIndepC_holds Formalism.L2.SG.Closed.AmpWellDefC_holds
    Formalism.L2.SG.Closed.AbsConvC_outright Formalism.L2.SG.Closed.KExpansionC_holds

theorem absConvTied_holds : Formalism.L2.SG.RowsConc.AbsConvTied :=
  Formalism.L2.SG.RowsConc.absConvTied_of_full Formalism.L2.SG.Closed.FoldOKC_outright Formalism.L2.SG.Closed.FundExistsC_holds
    Formalism.L2.SG.Closed.OOIntAllC_outright Formalism.L2.SG.Closed.AbsConvC_outright

variable (C0 : ℝ)

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

theorem theoremS_link_zero (𝒞 : FamClass) (sel : SSel 𝒞)
    (hWu : Formalism.L2.SG.Pf.WuDecayOfGap) (hRF : Formalism.L2.SG.RowsDef.RowsFinDim)
    (hLoc : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : Fm.x1 < x) (h0 : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.SG.Pf.LocCP.LocTied (Fm.D x i))
    (hTF : Closed 𝒞 fun Fm _ => PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0)
    (c30 : List ℝ → CountingConstants) (h1 : 1 ≤ C0)
    (hc30 : ∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A)
    (hRes : Closed 𝒞 fun Fm _ => ResidEv Fm)
    (hTy : Formalism.L2.SG.KappaOffDiagonal.TypeC) (hNG : Formalism.L2.SG.RowsConc.RowNGC) (hM : Formalism.L2.SG.RowsConc.RowMainEqC)
    (hLp : LoopRowS C0 𝒞 sel)
    (hO : Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, TheoremSSelected Fm C0 (sel Fm hc))
    (S30 : Closed 𝒞 fun Fm _ => CountE.ShareFamilyAtConstant CountE.PLev Fm (c30 Fm.cOut).Cres (c30 Fm.cOut).n0 (c30 Fm.cOut).A
      (c30 Fm.cOut).Cb (c30 Fm.cOut).C (c30 Fm.cOut).c (c30 Fm.cOut).cb)
    (A30 : Closed 𝒞 fun Fm _ => PlaceDegreeData.AdmF Fm (c30 Fm.cOut).Cres) :
    Closed 𝒞 fun Fm _ => TuSize Fm → Formalism.MainNotions.LinkS Fm C0 :=
  have hFX := Formalism.L2.SG.Pf.finXC_of hWu hRF
  have hOK := selOK_of C0 hFX hWu sel hLoc hTF
  have hE : Closed 𝒞 fun Fm _ => ConcEv C0 Fm :=
    closed_with hOK (fun _ => 0) (fun _ => 0) fun Fm _ hc h _ _ _ => concEv_of_sel C0 (h hc)
  have hRows : Closed 𝒞 fun Fm _ => ∃ xR : ℝ, ∀ x ≥ xR, Fm.x1 < x → ∀ i : Fm.Ix x, ∃ X : RowsAut,
      CountE.RowsTieP CountE.PLev (Fm.D x i) X :=
    closed_of_th (fun _ => 0) (fun _ => 0) fun Fm _ hc _ _ _ =>
      ⟨(sel Fm hc).1, fun x hx0 hx i => ⟨_, rowsTieP_of ((sel Fm hc).2 x hx hx0 i)⟩⟩
  linkS_concreteEv 𝒞 C0 c30 h1 hc30 hRes hRows (hypOwnE_kppOff C0 Formalism.L2.SG.Closed.KppOffC_holds hE)
    (hypOwnE_kppDiag C0 (Formalism.L2.SG.KappaOffDiagonal.kloostermanDiagonal_of_type hTy) absConvTied_holds hE)
    (hypOwnS_off C0 Formalism.L2.SG.Closed.KppOffC_holds kExpTied_holds absConvTied_holds sel hOK hO)
    (closed_clDiag_of_selOK C0 (Formalism.L2.SG.RowsConc.diagonal_contribution_of_equal_words hNG hM) kExpTied_holds absConvTied_holds sel hOK hLp) S30 A30

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

theorem theoremS_link (𝒞 : FamClass) (sel : SSel 𝒞)
    (hWu : Formalism.L2.SG.Pf.WuDecayOfGap) (hRF : Formalism.L2.SG.RowsDef.RowsFinDim)
    (hLoc : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : Fm.x1 < x) (h0 : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.SG.Pf.LocCP.LocTied (Fm.D x i))
    (hTF : Closed 𝒞 fun Fm _ => PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0)
    (c30 : List ℝ → CountingConstants) (h1 : 1 ≤ C0)
    (hc30 : ∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A)
    (hRes : Closed 𝒞 fun Fm _ => ResidEv Fm)
    (hTy : Formalism.L2.SG.KappaOffDiagonal.TypeC) (hNG : Formalism.L2.SG.RowsConc.RowNGC) (hM : Formalism.L2.SG.RowsConc.RowMainEqC)
    (hLp : LoopRowS C0 𝒞 sel)
    (hT : TheoremSSingle)
    (hRw : Closed 𝒞 fun Fm _ => OwnEv Fm fun C' Cl x i =>
      AdmissibleBoundsFromSource.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu →
        Formalism.L2.SG.Pf.SzHypOf.SzRowsAt (Fm.D x i))
    (hThr : ∀ CA : ℝ, 1 ≤ CA → Closed 𝒞 fun Fm _ => OwnEv Fm fun C' Cl x i =>
      AdmissibleBoundsFromSource.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu →
        ∀ u u' : (Fm.D x i).what₂.Word, u ≠ u' → Formalism.L2.SG.Pf.SzHypOf.ThresholdAtPlaces CA (Fm.D x i) u u')
    (aF : List ℝ → ℝ)
    (hA : Closed 𝒞 fun Fm _ => 1 ≤ aF Fm.cOut ∧ OwnEv Fm fun C' Cl x i =>
      AdmissibleBoundsFromSource.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu → Formalism.MainNotions.Sizes3b (Fm.D x i) (aF Fm.cOut))
    (S30 : Closed 𝒞 fun Fm _ => CountE.ShareFamilyAtConstant CountE.PLev Fm (c30 Fm.cOut).Cres (c30 Fm.cOut).n0 (c30 Fm.cOut).A
      (c30 Fm.cOut).Cb (c30 Fm.cOut).C (c30 Fm.cOut).c (c30 Fm.cOut).cb)
    (A30 : Closed 𝒞 fun Fm _ => PlaceDegreeData.AdmF Fm (c30 Fm.cOut).Cres) :
    Closed 𝒞 fun Fm _ => TuSize Fm → Formalism.MainNotions.LinkS Fm C0 :=
  have hOK := selOK_of C0 (Formalism.L2.SG.Pf.finXC_of hWu hRF) hWu sel hLoc hTF
  theoremS_link_zero C0 𝒞 sel hWu hRF hLoc hTF c30 h1 hc30 hRes hTy hNG hM hLp
    (theoremS_selected_of_loops C0 hT h1 sel hOK (Formalism.L2.SG.Pf.SzHypOf.sizesRowS_of C0 sel hRw hThr) aF hA hLp
      absConvTied_holds) S30 A30

end Formalism.L2.SG.ThmSOwn
