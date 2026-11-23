import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LinkSPos
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFam
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ThresholdLevels

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2 Formalism.L2.SG.RowsConc

set_option linter.dupNamespace false

namespace Formalism.L2.SG.ThmSOwn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def TheoremSAtData (CA C0 CG CDel cT Cb Cn : ℝ) (k0 : ℕ) (C' Cl Cg cb Cw cTf CT C0f : ℝ) : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (T : Formalism.L2.SG.SpectralTiesReal.STies D) (u u' : D.what₂.Word), Formalism.BasicNotions.Ties D → u ≠ u' → 0 ≤ L.sc.b →
    Formalism.L2.SG.PoincareAmplitudeLowerBounds.SizesAt CA C0 CG CDel cT Cb Cn k0 D L T u u' →
    Formalism.MainNotions.S.Cnt.Hyp0 D L C' Cl Cg cb Cw cTf CT C0f → Formalism.MainNotions.S.Cnt.Stand D u u' →
    Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D L C' Cl Cg cb Cw cTf CT C0f →
    Formalism.L2.SG.ConcreteSettingExists.GapHyp D → Formalism.L2.SG.Pf.LocCP.LocTied D → TFrameAt D →
    (T.Y.tO u u').RowBig (epsL D) (ddC T.X T.Y u u') → (T.Y.tO u u').RowNotScalar (epsL D) (ddC T.X T.Y u u') →
    ‖(T.Y.tO u u').K0‖ ^ 2 ≤ (1 + (L.sc.b ^ 6)⁻¹) * ((D.duS u : ℝ) * (D.duS u') / D.what₂.Dstar)

def TheoremSDistinctWords : Prop :=
  ∀ Cthr : ℝ, ∃ C₄ CA C : ℝ, 1 ≤ C₄ ∧ Cthr ≤ CA ∧ 1 ≤ CA ∧ 0 ≤ C ∧ C ≤ CA ∧
    ∀ (C0 CG CDel cT Cb : ℝ), 1 ≤ C0 → 0 ≤ CG → 4 < CDel → 0 < cT → 0 < Cb → 1 < cT * Cb →
    ∃ k0 : ℕ, ∀ Cg cb Cw cTf CT C0f : ℝ, 0 < cb → 0 < cTf → ∃ Cn C'₀ Cl₀ : ℝ, 0 ≤ Cn ∧ ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
      TheoremSAtData CA C0 CG CDel cT Cb Cn k0 C' Cl Cg cb Cw cTf CT C0f

def TheoremSClosedConclusion : Prop :=
  ∀ Cthr : ℝ, ∃ C₄ CA C : ℝ, 1 ≤ C₄ ∧ Cthr ≤ CA ∧ 1 ≤ CA ∧ 0 ≤ C ∧ C ≤ CA ∧
    ∀ (C0 CG CDel cT Cb : ℝ), 1 ≤ C0 → 0 ≤ CG → 4 < CDel → 0 < cT → 0 < Cb → 1 < cT * Cb →
    ∃ k0 : ℕ, ∀ Cg cb Cw cTf CT C0f : ℝ, 0 < cb → 0 < cTf → ∃ Cn C'₀ Cl₀ : ℝ, 0 ≤ Cn ∧ ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : SizeData₂ D) (T : Formalism.L2.SG.SpectralTiesReal.STies D) (u u' : D.what₂.Word), Formalism.BasicNotions.Ties D → u ≠ u' → 0 ≤ L.sc.b →
      Formalism.L2.SG.PoincareAmplitudeLowerBounds.SizesAt CA C0 CG CDel cT Cb Cn k0 D L T u u' →
      Formalism.MainNotions.S.Cnt.Hyp0 D L C' Cl Cg cb Cw cTf CT C0f → Formalism.MainNotions.S.Cnt.Stand D u u' →
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D L C' Cl Cg cb Cw cTf CT C0f →
      Formalism.L2.SG.ConcreteSettingExists.GapHyp D → Formalism.L2.SG.Pf.LocCP.LocTied D → TFrameAt D →
      (T.Y.tO u u').RowBig (epsL D) (ddC T.X T.Y u u') → (T.Y.tO u u').RowNotScalar (epsL D) (ddC T.X T.Y u u') →
      ‖(T.Y.tO u u').K0‖ ^ 2 ≤ (1 + (L.sc.b ^ 6)⁻¹) * ((D.duS u : ℝ) * (D.duS u') / D.what₂.Dstar) ∧
      L.hsSq u u' ≤ (1 + L.sc.b ^ (-(6 : ℝ))) * (D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar

theorem theoremS_distinct_of_closed (h : TheoremSClosedConclusion) : TheoremSDistinctWords := by
  intro Cthr
  obtain ⟨C₄, CA, C, a1, a2, a3, a4, a5, hrest⟩ := h Cthr
  refine ⟨C₄, CA, C, a1, a2, a3, a4, a5, fun C0 CG CDel cT Cb b1 b2 b3 b4 b5 b6 => ?_⟩
  obtain ⟨k0, hk⟩ := hrest C0 CG CDel cT Cb b1 b2 b3 b4 b5 b6
  refine ⟨k0, fun Cg cb Cw cTf CT C0f hcb hcT => ?_⟩
  obtain ⟨Cn, C'₀, Cl₀, hn, hh⟩ := hk Cg cb Cw cTf CT C0f hcb hcT
  exact ⟨Cn, C'₀, Cl₀, hn, fun C' Cl c1 c2 D L T u u' hTs hne hb hS hH0 hSt hK hG hL hT hR1 hR2 =>
    (hh C' Cl c1 c2 D L T u u' hTs hne hb hS hH0 hSt hK hG hL hT hR1 hR2).1⟩

variable (C0 : ℝ)

theorem offDiagonalK0_of_rows (hT : TheoremSDistinctWords) (h1 : 1 ≤ C0) {𝒞 : FamClass} (sel : SSel 𝒞)
    (hOK : Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, SelOK C0 Fm (sel Fm hc))
    (hSz : SizesRowS C0 𝒞 sel) (aF : List ℝ → ℝ)
    (hA : Closed 𝒞 fun Fm _ => 1 ≤ aF Fm.cOut ∧ OwnEv Fm fun C' Cl x i =>
      AdmissibleBoundsFromSource.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu → Formalism.MainNotions.Sizes3b (Fm.D x i) (aF Fm.cOut))
    (hLp : LoopRowS C0 𝒞 sel) (hAbs : AbsConvTied) :
    Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, TheoremSSelected Fm C0 (sel Fm hc) := by
  obtain ⟨-, CA, -, -, -, hCA, -, -, hrest⟩ := hT 1
  have H : ∀ l : List ℝ, ∃ k0 : ℕ, 0 ≤ l.getD 17 0 → ∃ Cn C'₀ Cl₀ : ℝ, 0 ≤ Cn ∧ ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
      TheoremSAtData CA C0 (l.getD 17 0) 5 (1 / 2) 3 Cn k0 C' Cl (l.getD 6 0 + 1) (1 / 4) 3 (1 / 2) (l.getD 13 0) C0 := by
    intro l
    by_cases h : 0 ≤ l.getD 17 0
    · obtain ⟨k0, hk⟩ := hrest C0 (l.getD 17 0) 5 (1 / 2) 3 h1 h (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      exact ⟨k0, fun _ => hk _ _ _ _ _ _ (by norm_num) (by norm_num)⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose k0f hk0 using H
  have G : ∀ l : List ℝ, ∃ Cn C'₀ Cl₀ : ℝ, 0 ≤ l.getD 17 0 → 0 ≤ Cn ∧ ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
      TheoremSAtData CA C0 (l.getD 17 0) 5 (1 / 2) 3 Cn (k0f l) C' Cl (l.getD 6 0 + 1) (1 / 4) 3 (1 / 2) (l.getD 13 0) C0 := by
    intro l
    by_cases h : 0 ≤ l.getD 17 0
    · obtain ⟨Cn, a, b, hn, hh⟩ := hk0 l h
      exact ⟨Cn, a, b, fun _ => ⟨hn, hh⟩⟩
    · exact ⟨0, 0, 0, fun h' => absurd h' h⟩
  choose cnf c'f clf hG using G
  refine closed_with (hOK.and ((hSz CA hCA k0f cnf).and ((hLp aF).and hA))) (fun _ => 0)
    (fun l => max (max (c'f l) (clf l)) 29) fun Fm CH _ hQ _ ht1 ht2 hc => ?_
  obtain ⟨hQ1, hQ2, hQ3, hA1, hQ4⟩ := hQ
  obtain ⟨xa, Ha⟩ := hQ1 hc
  obtain ⟨xb, Hb⟩ := hQ2 hc
  obtain ⟨xc, Hc⟩ := hQ3 hc
  obtain ⟨xd, Hd⟩ := hQ4
  refine ⟨max (max xa xb) (max xc xd), fun x hx i hH hx1 h0 u u' hne => ?_⟩
  have hxa : xa ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxb : xb ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxc : xc ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxd : xd ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have e17 : (Fm.cOut ++ Fm.cMid CH).getD 17 0 = Fm.CGam := rfl
  have hCG : 0 ≤ (Fm.cOut ++ Fm.cMid CH).getD 17 0 := by
    rw [e17, ← Fm.CGam_eq x i]; exact (Fm.L x i).CGam_pos.le
  obtain ⟨-, hrow⟩ := hG (Fm.cOut ++ Fm.cMid CH) hCG
  have hC'a : c'f (Fm.cOut ++ Fm.cMid CH) ≤ sC' Fm := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht1
  have hCla : clf (Fm.cOut ++ Fm.cMid CH) ≤ sCl Fm := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht2
  have hC'29 : (29 : ℝ) ≤ sC' Fm := le_trans (le_max_right _ _) ht1
  have hCl29 : (29 : ℝ) ≤ sCl Fm := le_trans (le_max_right _ _) ht2
  have ok := Ha x hxa i hH hx1 h0
  have tie : ConcTie ((sel Fm hc).2 x hx1 h0 i).X ((sel Fm hc).2 x hx1 h0 i).Y :=
    (concKOf ((sel Fm hc).2 x hx1 h0 i) ok).tie
  have hCnt := Formalism.MainNotions.count_hypotheses_of_sizes (Fm.D x i) (Fm.L x i) (sC' Fm) (sCl Fm) (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0
    (aF Fm.cOut) hH.1 hH.2.1 hH.2.2 (by linarith) (by linarith) hA1 (Hd x hxd i hH) u u'
  have hAC := hAbs _ _ _ u u' tie
  obtain ⟨hRB, hRNS⟩ := Hc x hxc i hx1 h0 u u' hCnt tie hAC
  have hb0 : 0 ≤ (Fm.L x i).sc.b := le_trans zero_le_two (Formalism.MainNotions.S.two_le_scb _)
  exact hrow (sC' Fm) (sCl Fm) hC'a hCla (Fm.D x i) (Fm.L x i) ((sel Fm hc).2 x hx1 h0 i) u u' (Fm.ties x i) hne hb0
    (Hb x hxb i hH hx1 h0 u u' hne) ⟨hH.2.1, hH.1, hH.2.2⟩
    (Formalism.MainNotions.Stand_of _ _ _ _ _ _ _ _ _ _ hH.1 hH.2.1 (by linarith) u u')
    (Formalism.MainNotions.NonGenericAndKTwoTheorems.Hyp_of _ _ _ _ _ _ _ _ _ _ hH.1 hH.2.1 hH.2.2 (by linarith))
    (gap_hypothesis_of_hypotheses hH.2.1 (by linarith) hC'29) ok.2.2.2.2.2.1 ok.2.2.2.2.2.2 hRB hRNS

variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

theorem theoremS_transport_link_partner (𝒞 : FamClass) (sel : SSel 𝒞)
    (hWu : Formalism.L2.SG.Pf.WuDecayOfGap) (hRF : Formalism.L2.SG.RowsDef.RowsFinDim)
    (hLoc : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : Fm.x1 < x) (h0 : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.SG.Pf.LocCP.LocTied (Fm.D x i))
    (hInst : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : Fm.x1 < x) (h0 : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      InstTie ((sel Fm hc).2 x hx h0 i).X.B.I)
    (hQ : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : Fm.x1 < x) (h0 : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      1 ≤ qqI ((sel Fm hc).2 x hx h0 i).X.B.I)
    (hRk : Formalism.L2.SG.Pf.SzHypFam.RanksRow C0 𝒞)
    (c30 : List ℝ → CountingConstants) (h1 : 1 ≤ C0)
    (hc30 : ∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A)
    (hRes : Closed 𝒞 fun Fm _ => ResidEv Fm)
    (hTy : Formalism.L2.SG.RowsPos.TypeP) (hNG : Formalism.L2.SG.RowsPos.RowNGP) (hM : Formalism.L2.SG.RowsPos.RowMainEqP)
    (hLp : LoopRowS C0 𝒞 sel) (hT : TheoremSDistinctWords)
    (h30 : Closed 𝒞 fun Fm _ => CountE.CountAllPointsClass PLevT' Fm (c30 Fm.cOut).n0 (c30 Fm.cOut).A (c30 Fm.cOut).C
      (c30 Fm.cOut).c (c30 Fm.cOut).cb) :
    Closed 𝒞 fun Fm _ => TuSize Fm → Formalism.MainNotions.LinkS Fm C0 :=
  have hTF := Formalism.L2.SG.Pf.SzHypFam.hTF_of_ranks C0 hRk
  have hOK := selOK_of C0 (Formalism.L2.SG.Pf.finXC_of hWu hRF) hWu sel hLoc hTF
  theoremS_transport_link_zero C0 𝒞 sel hWu hRF hLoc hInst hQ hTF c30 h1 hc30 hRes hTy hNG hM hLp
    (offDiagonalK0_of_rows C0 hT h1 sel hOK
      (Formalism.L2.SG.Pf.SzHypOf.sizesRowS_of C0 sel (Formalism.L2.SG.Pf.SzHypFam.hRw_of_ranks C0 hRk)
        (Formalism.L2.SG.Pf.ThresholdLevels.thrRow_holds C0))
      (Formalism.L2.SG.Pf.SzHypFam.aSz C0) (Formalism.L2.SG.Pf.SzHypFam.hA_of_ranks C0 h1 hRk) hLp absConvTied_holds) h30

end Formalism.L2.SG.ThmSOwn
