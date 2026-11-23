import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocCC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_JA_LocLemmas
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStable2

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace LocOp

def lcChi (x : ℝ) : ℝ := Real.smoothTransition (2 * x - 1)

theorem lcChi_zero {x : ℝ} (hx : x < 1 / 2) : lcChi x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem lcChi_one {x : ℝ} (hx : 1 ≤ x) : lcChi x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem isCut0_lcChi : C6.IsCut0 lcChi :=
  ⟨Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const),
    ⟨1 / 2, by norm_num, fun _ hx => lcChi_zero hx⟩, fun _ hx => lcChi_one hx⟩

section gen

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem wR_lie {w : List (B.Mat k r)} (hw : ∀ X ∈ w, B.inLie k r X) :
    ∀ x ∈ Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR w, B.inLie k r x.2 :=
  fun x hx => Formalism.FourierDecayAlt.P.BetaSesquilinearity.lie_LR (u := []) (by simp) hw x (by simpa [Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL] using hx)

theorem rw_congr_GV {F₀ : Type} [NormedAddCommGroup F₀] [NormedSpace ℂ F₀] {O : Set (B.Mat k r)} (hO : IsOpen O)
    {f₁ f₂ : B.Mat k r → F₀} (h : ∀ g ∈ B.GV k r, g ∈ O → f₁ g = f₂ g) {w : List (B.Mat k r)}
    (hw : ∀ X ∈ w, B.inLie k r X) : ∀ g ∈ B.GV k r, g ∈ O → B.Rw w f₁ g = B.Rw w f₂ g := by
  intro g hg hgO
  rw [← Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw_wR, ← Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw_wR]
  exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw_congr_loc (wR_lie hw) hO h g hg hgO

theorem opApply_congr_GV (Θ : B.DiffOp k r Wp Wq) {O : Set (B.Mat k r)} (hO : IsOpen O)
    {f₁ f₂ : B.Mat k r → (Wq →L[ℂ] Wp)} (h : ∀ g ∈ B.GV k r, g ∈ O → f₁ g = f₂ g) :
    ∀ g ∈ B.GV k r, g ∈ O → B.opApply Θ f₁ g = B.opApply Θ f₂ g := by
  intro g hg hgO
  unfold B.opApply
  congr 1
  refine List.map_congr_left fun T _ => ?_
  rw [rw_congr_GV hO h T.word_lie g hg hgO]

theorem opAdj_congr_GV (Θ : B.DiffOp k r Wp Wq) {O : Set (B.Mat k r)} (hO : IsOpen O)
    {f₁ f₂ : B.Mat k r → (Wq →L[ℂ] Wp)} (h : ∀ g ∈ B.GV k r, g ∈ O → f₁ g = f₂ g) :
    ∀ g ∈ B.GV k r, g ∈ O → B.opAdj Θ f₁ g = B.opAdj Θ f₂ g := by
  intro g hg hgO
  unfold B.opAdj
  congr 1
  refine List.map_congr_left fun T _ => ?_
  have h' : ∀ x ∈ B.GV k r, x ∈ O → T.coefAdj x (f₁ x) = T.coefAdj x (f₂ x) := fun x hx hxO => by
    rw [h x hx hxO]
  have hrev : ∀ X ∈ T.word.reverse, B.inLie k r X := fun X hX => T.word_lie X (List.mem_reverse.1 hX)
  rw [rw_congr_GV hO h' hrev g hg hgO]

end gen

section place

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
  [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem rep (hAg : LT.AgreeOm) {S : C.HidaSetting E Wp Wq}
    {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ}
    {ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ} {m₀ : Fin S.f → B.Mat S.G.k S.G.r}
    {top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ}
    {Cb A₀ : ℝ} (hB : BuiltOW Cb S T f χ ν' m₀ top A₀) (v : Fin S.f) {A Bg δ : ℝ} {J : GFn S v}
    (hBg : 2 * ((S.G.r : ℝ) + 1) ≤ Bg) (hJ : LocCC S T v A Bg J) (hδ : 0 < δ) :
    ∃ F : GFn S v, B.CkOn ⊤ (B.GV S.G.k S.G.r) F ∧ CCg S v A Bg F ∧
      (∀ g ∈ B.GV S.G.k S.G.r, Gf S.G.k S.G.r (T v).base.z (T v).base.z' g < 3 * δ / 8 → F g = 0) ∧
      ∀ g ∈ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z', 3 * δ / 4 < Gf S.G.k S.G.r (T v).base.z (T v).base.z' g →
        J g = B.JF (T v).base F g := by
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  obtain ⟨F₀, hF₀c, hF₀g, hF₀e⟩ := hJ.2 (δ / 4) (by positivity)
  have hε : (0 : ℝ) < 3 * δ / 4 := by positivity
  obtain ⟨δ', -, hcut, -⟩ := Formalism.FourierDecayAlt.P.JCTx6.Lev0.isCutG_div isCut0_lcChi hε
  obtain ⟨hFc, hFg⟩ := gcut_graded (T v).base.z (T v).base.z' (fun x => lcChi (x / (3 * δ / 4))) (δ' * (3 * δ / 4))
    hcut hBg hF₀c hF₀g
  refine ⟨D.cutF (T v).base lcChi F₀ (3 * δ / 4), hFc, hFg, ?_, ?_⟩
  · intro g _ hg
    have h1 : Gf S.G.k S.G.r (T v).base.z (T v).base.z' g / (3 * δ / 4) < 1 / 2 := by
      rw [div_lt_iff₀ hε]; linarith
    simp [D.cutF, lcChi_zero h1]
  · intro g hg hG
    refine hAg _ _ _ _ (T v).base J _ (Set.Ioi (3 * δ / 4)) hJ.1 ?_ g hg hG
    intro q hq hGq
    have hGq' : 3 * δ / 4 < Gf S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base q) := hGq
    have hx : q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT := ⟨hq.1, by rw [hTT]; exact hq.2⟩
    rw [hF₀e q hx (by unfold GfP; linarith), Formalism.FourierDecayAlt.P.JCTx2.JF_cutF]
    have h1 : 1 ≤ Gf S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base q) / (3 * δ / 4) := by
      rw [le_div_iff₀ hε]; linarith
    rw [lcChi_one h1]
    simp

theorem isOpen_omPlus_inter_lt {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (c : ℝ) :
    IsOpen (Q.OmPlus k r z z' ∩ {g | c < Gf k r z z' g}) :=
  (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open z z').inter (isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.BetaSesquilinearity.Gf_cont z z'))

end place

end LocOp

namespace LocOp

section place2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
  [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem thr_of {k r : ℕ} {o : ℕ} {A d Bg : ℝ} (hd : 0 ≤ d) (hBg : 0 ≤ Bg)
    (hA : 12 * ((r : ℝ) + 1) * nDim k r ^ 2 + 6 * (r : ℝ) * (o : ℝ) + d + 2 * Bg * ((o : ℝ) + 1) ≤ A) :
    Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r (A - Bg * o) o := by
  have ho : (0 : ℝ) ≤ (o : ℝ) := Nat.cast_nonneg o
  have hBo : 0 ≤ Bg * (o : ℝ) := mul_nonneg hBg ho
  exact jdc_thrW o (A - Bg * o) d hd (by nlinarith)

end place2

end LocOp

theorem jALocOp_of_tools (hOp : LT.OpCCg) (hAg : LT.AgreeOm) (hTh : LT.ThetaJApply) : JALocOp := by
  refine ⟨12, 2, by norm_num, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top Cb A₀ hB v Θ d Bg A J hd hBg hAA hCut hA hJ hFF
  have hBg0 : 0 ≤ Bg := le_trans (by positivity) hBg
  have hBo : 0 ≤ Bg * (B.opOrder Θ : ℝ) := mul_nonneg hBg0 (Nat.cast_nonneg _)
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  refine ⟨hFF, fun δ hδ => ?_⟩
  obtain ⟨F, hFc, hFg, hFz, hFe⟩ := LocOp.rep hAg hB v hBg hJ hδ
  obtain ⟨⟨hc, hg⟩, -⟩ := hOp _ _ _ _ (T v).base Θ d Bg A (3 * δ / 8) F (by positivity) hBg0 hAA.1 hCut hFc hFg hFz
  refine ⟨B.opApply Θ F, hc, fun m => inCC_antiA (by linarith) (hg m), fun x hx hG => ?_⟩
  have hq : x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hx.1, hTT ▸ hx.2⟩
  have hgO := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq
  have hGx : 3 * δ / 4 < Gf S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base x) := by
    have : δ ≤ Gf S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base x) := hG
    linarith
  rw [LocOp.opApply_congr_GV Θ (LocOp.isOpen_omPlus_inter_lt (T v).base.z (T v).base.z' (3 * δ / 4)) (f₁ := J)
    (f₂ := B.JF (T v).base F) (fun g hg hgO => hFe g ⟨hg, hgO.1⟩ hgO.2) _ hgO.1 ⟨hgO.2, hGx⟩]
  have hIn : B.InCC (A - Bg * (B.opOrder Θ : ℝ)) (B.opOrder Θ) F := hFg (B.opOrder Θ)
  exact hTh _ _ _ _ (T v).base Θ _ F (LocOp.thr_of hd hBg0 hA) hAA.1 hAA.2 hFc hIn _ hgO

theorem jALocAdj_of_tools (hOp : LT.OpCCg) (hAg : LT.AgreeOm) (hTh : LT.ThetaJ) : JALocAdj := by
  refine ⟨12, 2, by norm_num, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top Cb A₀ hB v Θ d Bg A J hd hBg hAA hCut hA hJ hFF
  have hBg0 : 0 ≤ Bg := le_trans (by positivity) hBg
  have hBo : 0 ≤ Bg * (B.opOrder Θ : ℝ) := mul_nonneg hBg0 (Nat.cast_nonneg _)
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  refine ⟨hFF, fun δ hδ => ?_⟩
  obtain ⟨F, hFc, hFg, hFz, hFe⟩ := LocOp.rep hAg hB v hBg hJ hδ
  obtain ⟨-, ⟨hc, hg⟩⟩ := hOp _ _ _ _ (T v).base Θ d Bg A (3 * δ / 8) F (by positivity) hBg0 hAA.1 hCut hFc hFg hFz
  refine ⟨B.opAdj Θ F, hc, fun m => inCC_antiA (by linarith) (hg m), fun x hx hG => ?_⟩
  have hq : x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hx.1, hTT ▸ hx.2⟩
  have hgO := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq
  have hGx : 3 * δ / 4 < Gf S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base x) := by
    have : δ ≤ Gf S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base x) := hG
    linarith
  rw [LocOp.opAdj_congr_GV Θ (LocOp.isOpen_omPlus_inter_lt (T v).base.z (T v).base.z' (3 * δ / 4)) (f₁ := J)
    (f₂ := B.JF (T v).base F) (fun g hg hgO => hFe g ⟨hg, hgO.1⟩ hgO.2) _ hgO.1 ⟨hgO.2, hGx⟩]
  have hIn : B.InCC (A - Bg * (B.opOrder Θ : ℝ)) (B.opOrder Θ) F := hFg (B.opOrder Θ)
  set UU : Set (B.Mat S.G.k S.G.r) := {g | g ∈ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z' ∧
    3 * δ / 4 < Gf S.G.k S.G.r (T v).base.z (T v).base.z' g} with hUU
  have hCkJ : B.CkOn ⊤ (JF.Om S.G.k S.G.r (T v).base.z (T v).base.z') J := jdc_ckOn_om _ _ hJ.1.1
  have hCk : B.CkOn ⊤ UU (B.JF (T v).base F) := by
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hc', he⟩ := hCkJ g₀ hg₀.1
    refine ⟨U ∩ (Q.OmPlus S.G.k S.G.r (T v).base.z (T v).base.z' ∩
        {g | 3 * δ / 4 < Gf S.G.k S.G.r (T v).base.z (T v).base.z' g}), f',
      hU.inter (LocOp.isOpen_omPlus_inter_lt _ _ _), ⟨hgU, hg₀.1.2, hg₀.2⟩, hc'.mono Set.inter_subset_left, fun g hg hgG => ?_⟩
    rw [← hFe g ⟨hgG, hg.2.1⟩ hg.2.2]
    exact he g hg.1 hgG
  exact (hTh _ _ _ _ (T v).base Θ _ F UU (LocOp.thr_of hd hBg0 hA) hAA.1 hAA.2 hFc hIn (fun g hg => hg.1)
    (Formalism.FourierDecayAlt.P.BetaSesquilinearity.sCkOn_mono le_top hCk)).2 _ ⟨hgO, hGx⟩

end Formalism.FourierDecayAlt.P.CutMP.JA

end
