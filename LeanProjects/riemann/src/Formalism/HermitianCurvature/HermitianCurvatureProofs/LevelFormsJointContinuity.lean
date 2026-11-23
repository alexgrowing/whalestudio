import Formalism.HermitianCurvature.HermitianCurvatureProofs.OmLongContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CcCoefMMono
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermPartsCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FormLevLimit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondDefectNonneg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LimitOfModuleForms
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BuiltBoundsCompactOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleWordMemBoundedLetterLists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCutInside
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.LastBlockContinuity

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBE NumberField

theorem formLev_tendsto {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter) (N : ℕ) (hw : w.length ≤ N)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) {ι : Type} (l : Filter ι)
    (x y : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (xn yn : ι → Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (Bd : ℝ) (dn : ι → ℝ)
    (hdn : Tendsto dn l (𝓝 0))
    (hx : ∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (x e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (x e) Bd)
    (hy : ∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (y e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (y e) Bd)
    (hev : ∀ᶠ n in l, (∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (yn n e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (yn n e) Bd) ∧
      (∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (xn n e - x e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (xn n e - x e) (dn n)) ∧
      (∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (yn n e - y e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (yn n e - y e) (dn n))) :
    Tendsto (fun n => D.formLev T s j w (xn n) (yn n)) l (𝓝 (D.formLev T s j w x y)) := by
  have hAu : P5.Auser P0 w.length + 1 ≤ P5.Auser P0 N + 1 := by linarith [auser_mono P0 hw]
  have hmu : P5.mmUser P0 w.length ≤ P5.mmUser P0 N := mmUser_mono P0 hw
  have hS := Formalism.FourierDecayAlt.P.level_form_sesquilinear_moderate Wp Wq P0 T s j w (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ hε₀ hAu hmu
  obtain ⟨Cf, hCf0, hCf⟩ := Formalism.FourierDecayAlt.P.JCx4.formLev_bound_mm P0 T s j w (P5.Auser P0 N + 1 + 1) (by linarith)
  have hmm5 : 5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length ≤ P5.mmUser P0 N := by
    have := Formalism.FourierDecayAlt.P.JCx2.pd_thr_mm P0 j N (P5.mmUser P0 N) le_rfl
    have h2 : (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length ≤ (2 * (P0.r - (j : ℕ)) + P0.k + 1) * N :=
      Nat.mul_le_mul_left _ hw
    omega
  have h5 : 5 ≤ P5.mmUser P0 N := by unfold P5.mmUser; omega
  have hu : ∀ (u : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (cu : ℝ),
      (∀ e, B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (u e) cu) →
      ∀ e, B.CCle (P5.Auser P0 N + 1 + 1 - 1) (5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (u e) cu := by
    intro u cu h e
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m hmm5 (h e))
  have hv : ∀ (u : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (cu : ℝ),
      (∀ e, B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (u e) cu) →
      ∀ e, B.CCle (P5.Auser P0 N + 1 + 1 - 1 - 2 * (w.length : ℝ)) 5 (u e) cu := by
    intro u cu h e
    have hw0 : (0 : ℝ) ≤ w.length := Nat.cast_nonneg _
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m h5 (h e))
  have key : ∀ n, (∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (yn n e)) →
      (∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (xn n e - x e)) →
      (∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (yn n e - y e)) →
      D.formLev T s j w (xn n) (yn n) - D.formLev T s j w x y =
        D.formLev T s j w (xn n - x) (yn n) + D.formLev T s j w x (yn n - y) := by
    intro n hyn hdx hdy
    have e1 : xn n = x + (1 : ℂ) • (xn n - x) := by simp
    have e2 : yn n = y + (1 : ℂ) • (yn n - y) := by simp
    have s1 := (hS x (xn n - x) (yn n) 1 (fun e => (hx e).1) hdx hyn).1
    have s2 := (hS y (yn n - y) x 1 (fun e => (hy e).1) hdy (fun e => (hx e).1)).2
    rw [← e1] at s1
    rw [← e2] at s2
    rw [s1, s2]
    simp
    ring
  have hbd : ∀ᶠ n in l, ‖D.formLev T s j w (xn n) (yn n) - D.formLev T s j w x y‖ ≤ 2 * Cf * Bd * dn n := by
    filter_upwards [hev] with n hn
    obtain ⟨hyn, hdx, hdy⟩ := hn
    rw [key n (fun e => (hyn e).1) (fun e => (hdx e).1) (fun e => (hdy e).1)]
    have b1 := hCf (xn n - x) (yn n) (dn n) Bd (hu _ _ fun e => (hdx e).2) (hv _ _ fun e => (hyn e).2)
    have b2 := hCf x (yn n - y) Bd (dn n) (hu _ _ fun e => (hx e).2) (hv _ _ fun e => (hdy e).2)
    calc _ ≤ ‖D.formLev T s j w (xn n - x) (yn n)‖ + ‖D.formLev T s j w x (yn n - y)‖ := norm_add_le _ _
      _ ≤ Cf * dn n * Bd + Cf * Bd * dn n := add_le_add b1 b2
      _ = 2 * Cf * Bd * dn n := by ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n => 2 * Cf * Bd * dn n) l (𝓝 0) := by
    simpa using hdn.const_mul (2 * Cf * Bd)
  exact squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) hbd hlim

theorem continuousOn_weight_product (k r : ℕ) (fr : ℕ → ℕ → ℝ) (hfr : ∀ b s, 0 < fr b s) (m : ℕ) :
    ∀ (H : C.LPt) (b : ℕ), ContinuousOn (fun q : ℝ × ℂ => C.nAux k r q.1 fr b (H ++ [(m, q.2)]))
      (Set.univ ×ˢ {0}ᶜ)
  | [], b => by
    simp only [List.nil_append, C.nAux, mul_one]
    split_ifs
    · exact (continuous_fst.pow _).continuousOn
    · refine ContinuousOn.zpow₀ ?_ _ ?_
      · exact (continuous_const.mul (continuous_norm.comp continuous_snd)).continuousOn
      · intro q hq
        left
        exact mul_ne_zero (hfr b m).ne' (norm_ne_zero_iff.mpr hq.2)
  | (s, t) :: H, b => by
    simp only [List.cons_append, C.nAux]
    refine ContinuousOn.mul ?_ (continuousOn_weight_product k r fr hfr m H (b + s))
    split_ifs
    · exact (continuous_fst.pow _).continuousOn
    · exact continuousOn_const

section setting

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem fr_pos (S : C.HidaSetting E Wp Wq) (b s : ℕ) : 0 < S.fr b s := by
  unfold C.HidaSetting.fr
  exact Real.rpow_pos_of_pos (Formalism.FourierDecayAlt.P.PBD.rd_pos' E) _

theorem nnS_cont (S : C.HidaSetting E Wp Wq) (P : C.LPt) (m : ℕ) :
    ContinuousOn (fun c : ℂ => PBL.nnS S (P ++ [(m, c)])) {0}ᶜ := by
  have h1 := continuousOn_weight_product S.G.k S.G.r S.fr (fr_pos S) m P 1
  have hmap : Set.MapsTo (fun c : ℂ => ((Complex.normSq c - S.T * S.T' : ℝ), c)) {0}ᶜ (Set.univ ×ˢ {0}ᶜ) :=
    fun c hc => ⟨Set.mem_univ _, hc⟩
  have h2 := h1.comp (Continuous.continuousOn (by fun_prop)) hmap
  refine h2.congr fun c _ => ?_
  simp only [Function.comp, PBL.nnS, C.nLoc]
  congr 1
  simp [D.ptGG, D.ptLast]

end setting

section place

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem isLocPt_app {h : C.LPt} (hh : ∀ b ∈ h, 1 ≤ b.1 ∧ b.2 ≠ 0) {m : ℕ} (hm : 1 ≤ m) {c : ℂ} (hc : c ≠ 0)
    {i : ℕ} (hsz : D.ptSize h + m = i) : D.IsLocPt (h ++ [(m, c)]) i := by
  refine ⟨fun b hb => ?_, ?_⟩
  · rcases List.mem_append.1 hb with hb | hb
    · exact hh b hb
    · rw [List.mem_singleton] at hb
      subst hb
      exact ⟨hm, hc⟩
  · rw [← hsz]
    simp [D.ptSize]

theorem heads_of_loc {h : C.LPt} {m : ℕ} {c : ℂ} {i : ℕ} (hl : D.IsLocPt (h ++ [(m, c)]) i) :
    ∀ b ∈ h, 1 ≤ b.1 ∧ b.2 ≠ 0 := fun b hb => hl.1 b (List.mem_append_left _ hb)

theorem rrTop_cont (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef p.T.base F)
    (Cb : ℝ) (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (w : List C.Letter) (hw : KB.CutWord P p.l0 w)
    (h h' : C.LPt) (m : ℕ) (hm : 1 ≤ m) (hsz : D.ptSize h + m = P.r + 1) (hsz' : D.ptSize h' + m = P.r + 1) :
    ContinuousOn (fun cc : ℂ × ℂ => p.RR F (P.r + 1) w (h ++ [(m, cc.1)]) (h' ++ [(m, cc.2)]))
      (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)) := by
  by_cases hh : (∀ b ∈ h, 1 ≤ b.1 ∧ b.2 ≠ 0) ∧ (∀ b ∈ h', 1 ≤ b.1 ∧ b.2 ≠ 0)
  · obtain ⟨hh1, hh2⟩ := hh
    have hform : ∀ cc ∈ (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)),
        p.RR F (P.r + 1) w (h ++ [(m, cc.1)]) (h' ++ [(m, cc.2)]) =
          (if w = [] then B.hsInner (p.V F (h ++ [(m, cc.1)])) (p.V F (h' ++ [(m, cc.2)]))
            else Top.topOf P p.l0 p.T p.ν' p.m₀ p.Θ p.TP F w (h ++ [(m, cc.1)]) (h' ++ [(m, cc.2)])) := by
      intro cc hcc
      have l1 := isLocPt_app hh1 hm hcc.1 hsz
      have l2 := isLocPt_app hh2 hm hcc.2 hsz'
      unfold KB.Pl.RR D.RRplace
      rw [dif_pos ⟨l1, l2⟩, dif_neg (by omega), if_pos rfl]
      rfl
    by_cases hw0 : w = []
    · refine (hsV_continuousOn P p F hF h h' hh1 hh2 m hm hsz hsz').congr fun cc hcc => ?_
      rw [hform cc hcc, if_pos hw0]
    · refine (topOf_continuousOn P p F hF Cb hCb w hw h h' hh1 hh2 m hm hsz hsz').congr fun cc hcc => ?_
      rw [hform cc hcc, if_neg hw0]
  · refine (continuousOn_const (c := (0 : ℂ))).congr fun cc _ => ?_
    exact PBL.rr_zero_of_not p F _ w _ _ (fun hl => hh ⟨heads_of_loc hl.1, heads_of_loc hl.2⟩)

end place

section below

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem hc_app {r i : ℕ} (h0 : C.LPt) (m : ℕ) (hsz : D.ptSize h0 + m = i) (t : ℂ) :
    r - i = r - D.ptSize (h0 ++ [(m, t)]) := by
  rw [Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append, hsz]

def SlcOK {k r : ℕ} (T : D.LevTower k r Wp Wq) (χ : ℝ → ℝ) (ε : ℝ) (i : ℕ) (hi : i ≤ r) (w : List C.Letter)
    (N : ℕ) (P0 : M.Par) (h0 : C.LPt) (m : ℕ) (hsz : D.ptSize h0 + m = i) (hcf : B.Mat k r → (Wq →L[ℂ] Wp))
    (t0 : ℂ) : Prop :=
  ∃ ε' : ℝ, 0 < ε' ∧ ∀ a : Wd.Ix (Fin w.length), ∃ (δ Kb : ℝ) (Dd : ℂ → ℝ), 0 < δ ∧ Tendsto Dd (𝓝 t0) (𝓝 0) ∧
    ∀ t : ℂ, dist t t0 < δ → t ≠ 0 ∧
      JC.CCCoefM (T.bs i) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε' (xs T χ ε i hi w (h0 ++ [(m, t)]) (hc_app h0 m hsz t) hcf a) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (xs T χ ε i hi w (h0 ++ [(m, t)]) (hc_app h0 m hsz t) hcf a) Kb ∧
      JC.CCCoefM (T.bs i) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε'
        (xs T χ ε i hi w (h0 ++ [(m, t)]) (hc_app h0 m hsz t) hcf a - xs T χ ε i hi w (h0 ++ [(m, t0)]) (hc_app h0 m hsz t0) hcf a) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N)
        (xs T χ ε i hi w (h0 ++ [(m, t)]) (hc_app h0 m hsz t) hcf a - xs T χ ε i hi w (h0 ++ [(m, t0)]) (hc_app h0 m hsz t0) hcf a) (Dd t)

theorem ccCoefM_le {k r : ℕ} {Bs : B.RealPlaceData k r Wp Wq} {A : ℝ} {mm : ℕ} {ε₁ ε₂ : ℝ}
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (h : JC.CCCoefM Bs A mm ε₁ F) (hle : ε₂ ≤ ε₁) : JC.CCCoefM Bs A mm ε₂ F :=
  ⟨h.1, h.2.1, fun g hg hne => le_trans hle (h.2.2 g hg hne)⟩

theorem rrBelow_cont (P : M.Par) (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (ε : ℝ) (hcf : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (i : ℕ) (hi : i ≤ P.r) (w : List C.Letter) (N : ℕ) (hw : w.length ≤ N) (h h' : C.LPt) (m : ℕ) (hm : 1 ≤ m)
    (hsz : D.ptSize h + m = i) (hsz' : D.ptSize h' + m = i)
    (hS : (∀ b ∈ h, 1 ≤ b.1 ∧ b.2 ≠ 0) → ∀ t0 : ℂ, t0 ≠ 0 → SlcOK p.T χ ε i hi w N P h m hsz hcf t0)
    (hS' : (∀ b ∈ h', 1 ≤ b.1 ∧ b.2 ≠ 0) → ∀ t0 : ℂ, t0 ≠ 0 → SlcOK p.T χ ε i hi w N P h' m hsz' hcf t0) :
    ContinuousOn (fun cc : ℂ × ℂ => p.RR (D.cutF p.T.base χ hcf ε) i w (h ++ [(m, cc.1)]) (h' ++ [(m, cc.2)]))
      (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)) := by
  by_cases hh : (∀ b ∈ h, 1 ≤ b.1 ∧ b.2 ≠ 0) ∧ (∀ b ∈ h', 1 ≤ b.1 ∧ b.2 ≠ 0)
  · obtain ⟨hh1, hh2⟩ := hh
    set S : Set (ℂ × ℂ) := ({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ) with hSdef
    have hlt : i < P.r + 1 := by omega
    have hform : ∀ cc ∈ S, p.RR (D.cutF p.T.base χ hcf ε) i w (h ++ [(m, cc.1)]) (h' ++ [(m, cc.2)]) =
        D.formLev p.T (M.sgn P p.l0) ⟨i, hlt⟩ w
          (fun a => xs p.T χ ε i hi w (h ++ [(m, cc.1)]) (hc_app h m hsz cc.1) hcf a)
          (fun a => xs p.T χ ε i hi w (h' ++ [(m, cc.2)]) (hc_app h' m hsz' cc.2) hcf a) := by
      intro cc hcc
      have l1 := isLocPt_app hh1 hm hcc.1 hsz
      have l2 := isLocPt_app hh2 hm hcc.2 hsz'
      unfold KB.Pl.RR D.RRplace
      rw [dif_pos ⟨l1, l2⟩, dif_pos hi]
      rfl
    rintro ⟨c0, c0'⟩ ⟨hc0, hc0'⟩
    obtain ⟨ε1, hε1, H1⟩ := hS hh1 c0 hc0
    obtain ⟨ε2, hε2, H2⟩ := hS' hh2 c0' hc0'
    choose δ1 Kb1 Dd1 hδ1 hDd1 hb1 using H1
    choose δ2 Kb2 Dd2 hδ2 hDd2 hb2 using H2
    set ε₀ : ℝ := min ε1 ε2 with hε₀
    have hε₀p : 0 < ε₀ := lt_min hε1 hε2
    set Bd : ℝ := ∑ a, (|Kb1 a| + |Kb2 a|) with hBd
    have hK1 : ∀ a, Kb1 a ≤ Bd := fun a => le_trans (le_abs_self _) (le_trans (le_add_of_nonneg_right (abs_nonneg _))
      (Finset.single_le_sum (f := fun b => |Kb1 b| + |Kb2 b|) (fun b _ => by positivity) (Finset.mem_univ a)))
    have hK2 : ∀ a, Kb2 a ≤ Bd := fun a => le_trans (le_abs_self _) (le_trans (le_add_of_nonneg_left (abs_nonneg _))
      (Finset.single_le_sum (f := fun b => |Kb1 b| + |Kb2 b|) (fun b _ => by positivity) (Finset.mem_univ a)))
    set dn : ℂ × ℂ → ℝ := fun cc => ∑ a, (Dd1 a cc.1 + Dd2 a cc.2) with hdn
    have hdnT : Tendsto dn (𝓝[S] (c0, c0')) (𝓝 0) := by
      have h1 : Tendsto dn (𝓝 (c0, c0')) (𝓝 (∑ _a : Wd.Ix (Fin w.length), ((0 : ℝ) + 0))) :=
        tendsto_finsetSum _ fun a _ =>
          ((hDd1 a).comp (continuous_fst.tendsto (c0, c0'))).add ((hDd2 a).comp (continuous_snd.tendsto (c0, c0')))
      simp only [add_zero, Finset.sum_const_zero] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    have hball : ∀ᶠ cc in 𝓝[S] (c0, c0'), ∀ a, dist cc.1 c0 < δ1 a ∧ dist cc.2 c0' < δ2 a := by
      refine nhdsWithin_le_nhds (Filter.eventually_all.2 fun a => ?_)
      exact ((continuous_fst.tendsto (c0, c0')).eventually (Metric.ball_mem_nhds c0 (hδ1 a))).and
        ((continuous_snd.tendsto (c0, c0')).eventually (Metric.ball_mem_nhds c0' (hδ2 a)))
    have hs1 : dist c0 c0 < 0 + 1 := by rw [dist_self]; norm_num
    have hx0 : ∀ a, JC.CCCoefM (p.T.bs (i : ℕ)) (P5.Auser P N + 1) (P5.mmUser P N) ε₀
          (xs p.T χ ε i hi w (h ++ [(m, c0)]) (hc_app h m hsz c0) hcf a) ∧
        B.CCle (P5.Auser P N + 1) (P5.mmUser P N) (xs p.T χ ε i hi w (h ++ [(m, c0)]) (hc_app h m hsz c0) hcf a) Bd := by
      intro a
      obtain ⟨-, q1, q2, -, -⟩ := hb1 a c0 (by rw [dist_self]; exact hδ1 a)
      exact ⟨ccCoefM_le q1 (min_le_left _ _), Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c q2 (hK1 a)⟩
    have hy0 : ∀ a, JC.CCCoefM (p.T.bs (i : ℕ)) (P5.Auser P N + 1) (P5.mmUser P N) ε₀
          (xs p.T χ ε i hi w (h' ++ [(m, c0')]) (hc_app h' m hsz' c0') hcf a) ∧
        B.CCle (P5.Auser P N + 1) (P5.mmUser P N) (xs p.T χ ε i hi w (h' ++ [(m, c0')]) (hc_app h' m hsz' c0') hcf a) Bd := by
      intro a
      obtain ⟨-, q1, q2, -, -⟩ := hb2 a c0' (by rw [dist_self]; exact hδ2 a)
      exact ⟨ccCoefM_le q1 (min_le_right _ _), Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c q2 (hK2 a)⟩
    have hT := formLev_tendsto P p.T (M.sgn P p.l0) ⟨i, hlt⟩ w N hw ε₀ hε₀p (𝓝[S] (c0, c0'))
      (fun a => xs p.T χ ε i hi w (h ++ [(m, c0)]) (hc_app h m hsz c0) hcf a)
      (fun a => xs p.T χ ε i hi w (h' ++ [(m, c0')]) (hc_app h' m hsz' c0') hcf a)
      (fun cc a => xs p.T χ ε i hi w (h ++ [(m, cc.1)]) (hc_app h m hsz cc.1) hcf a)
      (fun cc a => xs p.T χ ε i hi w (h' ++ [(m, cc.2)]) (hc_app h' m hsz' cc.2) hcf a) Bd dn hdnT hx0 hy0 ?_
    · have hcc0 : ((c0, c0') : ℂ × ℂ) ∈ S := ⟨hc0, hc0'⟩
      have e0 : p.RR (D.cutF p.T.base χ hcf ε) i w (h ++ [(m, c0)]) (h' ++ [(m, c0')]) =
          D.formLev p.T (M.sgn P p.l0) ⟨i, hlt⟩ w
            (fun a => xs p.T χ ε i hi w (h ++ [(m, c0)]) (hc_app h m hsz c0) hcf a)
            (fun a => xs p.T χ ε i hi w (h' ++ [(m, c0')]) (hc_app h' m hsz' c0') hcf a) := hform (c0, c0') hcc0
      show Tendsto _ (𝓝[S] (c0, c0')) (𝓝 (p.RR (D.cutF p.T.base χ hcf ε) i w (h ++ [(m, c0)]) (h' ++ [(m, c0')])))
      rw [e0]
      refine hT.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with cc hcc
      exact (hform cc hcc).symm
    · filter_upwards [hball] with cc hcc
      have hn1 : ∀ b, 0 ≤ Dd1 b cc.1 := fun b =>
        Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg (hb1 b cc.1 (hcc b).1).2.2.2.2
      have hn2 : ∀ b, 0 ≤ Dd2 b cc.2 := fun b =>
        Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg (hb2 b cc.2 (hcc b).2).2.2.2.2
      have hle1 : ∀ a, Dd1 a cc.1 ≤ dn cc := fun a =>
        le_trans (le_add_of_nonneg_right (hn2 a))
          (Finset.single_le_sum (f := fun b => Dd1 b cc.1 + Dd2 b cc.2) (fun b _ => add_nonneg (hn1 b) (hn2 b))
            (Finset.mem_univ a))
      have hle2 : ∀ a, Dd2 a cc.2 ≤ dn cc := fun a =>
        le_trans (le_add_of_nonneg_left (hn1 a))
          (Finset.single_le_sum (f := fun b => Dd1 b cc.1 + Dd2 b cc.2) (fun b _ => add_nonneg (hn1 b) (hn2 b))
            (Finset.mem_univ a))
      refine ⟨fun a => ?_, fun a => ?_, fun a => ?_⟩
      · obtain ⟨-, q1, q2, -, -⟩ := hb2 a cc.2 (hcc a).2
        exact ⟨ccCoefM_le q1 (min_le_right _ _), Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c q2 (hK2 a)⟩
      · obtain ⟨-, -, -, q3, q4⟩ := hb1 a cc.1 (hcc a).1
        exact ⟨ccCoefM_le q3 (min_le_left _ _), Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c q4 (hle1 a)⟩
      · obtain ⟨-, -, -, q3, q4⟩ := hb2 a cc.2 (hcc a).2
        exact ⟨ccCoefM_le q3 (min_le_right _ _), Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c q4 (hle2 a)⟩
  · refine (continuousOn_const (c := (0 : ℂ))).congr fun cc _ => ?_
    exact PBL.rr_zero_of_not p _ _ w _ _ (fun hl => hh ⟨heads_of_loc hl.1, heads_of_loc hl.2⟩)

end below

section final

theorem ptSize_toStd' (r : ℕ) (g : ℝ) : ∀ (b : ℕ) (P : C.LPt), D.ptSize (D.toStd r g b P) = D.ptSize P
  | _, [] => rfl
  | b, (s, t) :: rest => by
    have ih := ptSize_toStd' r g (b + s) rest
    simp only [D.toStd, D.ptSize, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]

theorem bS_app {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (P : C.LPt) (m : ℕ) (c : ℂ) :
    PBL.bS S (P ++ [(m, c)]) = PBL.bS S (P ++ [(m, 1)]) := by
  simp [PBL.bS, D.bSt]

theorem level_forms_joint_continuity : GermFibreKernels.KerContB := by
  unfold GermFibreKernels.KerContB
  intro Cb
  obtain ⟨Cs, hCs0, hSQ⟩ := sliceContQ
  obtain ⟨c1, h1⟩ := limit_of_module_forms Cb
  refine ⟨max (Cs + 1) c1, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB n v
  have hB' := hB
  obtain ⟨-, -, -, hcut, -, -, -, -, -, -, hGo, -, -, -, hA, hv⟩ := hB'
  have hCI : KB.CutInside S := PBCut.cutInside_of_built hB
  have hgpos := PBL.g_pos_of_built hB
  obtain ⟨hl0, hInD, -, hCk, hCC⟩ := hv v
  have hcpt : ∀ ε, 0 < ε → KB.CptCoef (p v).T.base (PBASM.cutSeq S p f χ n v ε) := by
    intro ε hε
    refine (h1 (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (f v) χ ε A₀ S.Ntop PBASM.cutN
      (by rw [hl0]; exact hInD) hcut hε hCk hCC (le_trans ?_ hA) (fun n g => rfl)).1 n
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) (by positivity)

  have hX1 : (1 : ℝ) ≤ (S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3 := by
    have h1' : (1 : ℝ) ≤ 2 * (S.G.r : ℝ) + S.G.k + 1 := by
      have : (0 : ℝ) ≤ S.G.r := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ S.G.k := Nat.cast_nonneg _
      linarith
    have : 1 ≤ (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3 := one_le_pow₀ h1'
    have : 0 ≤ (S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 := by positivity
    linarith
  have hR4 : 1 ≤ ((S.G.r : ℝ) + 1) ^ 4 := one_le_pow₀ (by have : (0 : ℝ) ≤ S.G.r := Nat.cast_nonneg _; linarith)
  have hA' : Cs * ((S.G.r : ℝ) + 1) ^ 4 *
      ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) ≤ A₀ - 1 := by
    have h1' : (Cs + 1) * ((S.G.r : ℝ) + 1) ^ 4 *
        ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) ≤ A₀ :=
      le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        (by positivity)) hA
    have h2 : 1 ≤ ((S.G.r : ℝ) + 1) ^ 4 *
        ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) := by nlinarith
    nlinarith

  have hk2 : 2 ≤ (D.parOf S v).k := (p v).hl.2.2
  set M := 3 * (11 * (S.Ntop * (2 * (D.parOf S v).r + (D.parOf S v).k + 1) ^ 2 +
    (2 * (D.parOf S v).r + (D.parOf S v).k + 1) ^ 3) + 5) with hM
  obtain ⟨bf, hbf⟩ := hCC M
  have hbf0 : 0 ≤ bf := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hbf
  have hbf' : B.CCle (A₀ - 1) M (f v) bf := Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) hbf
  obtain ⟨Kp, hKp0, hKp⟩ := Formalism.FourierDecayAlt.P.JCx2.pd_cut_ccle (k := (D.parOf S v).k) (r := (D.parOf S v).r)
    (E := Wq (S.pl v) →L[ℂ] Wp (S.pl v)) M
  set hn : B.Mat (D.parOf S v).k (D.parOf S v).r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) :=
    fun g => PBASM.cutN n g • f v g with hhn
  have hneq : hn = fun g => f v g + (-1 : ℂ) • (Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g • f v g) := by
    funext g
    simp only [hhn, PBE.cut_eq PBASM.cutN (fun n g => rfl) n g, sub_smul, one_smul]
    simp [sub_eq_add_neg]
  have hnC : B.CCle (A₀ - 1) M hn (bf + Kp * bf) := by
    rw [hneq]
    refine Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hbf'
      (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul (-1) (hKp _ (by positivity) A₀ (f v) bf hbf))) ?_
    have h1' : Kp * bf / ((n : ℝ) + 1) ≤ Kp * bf := div_le_self (by positivity) (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    simp only [norm_neg, norm_one, one_mul]
    linarith
  have hns : B.CkOn ⊤ (B.GV (D.parOf S v).k (D.parOf S v).r) hn := by
    rw [hneq]
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add hCk (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul (-1)
      (Formalism.FourierDecayAlt.P.JCx2.pd_smooth_smul (Formalism.FourierDecayAlt.P.JCx2.pd_psi_cd _) hCk))
  have hFn : ∀ ε, PBASM.cutSeq S p f χ n v ε = D.cutF (p v).T.base χ hn ε := by
    intro ε; funext g
    simp only [PBASM.cutSeq, D.cutF, hhn]
    rw [smul_comm]

  unfold GermFibreKernels.KerCont
  intro ε hε i hi a ha m hm P Q hP hQ
  have hGr : (PBL.setC S p (PBASM.cutSeq S p f χ n)).G.r = S.G.r := rfl
  rw [hGr] at hi
  obtain ⟨w, hw⟩ := ha
  have hlen : a.length ≤ S.Ntop := by rw [← hw]; exact le_trans (PBB.len_le_cnt S w v) w.2.2
  have hcw : KB.CutWord (D.parOf S v) (p v).l0 a := by rw [hl0, ← hw]; exact PBD.cutWord_of_adm S hGo hCI w v
  have hszP : D.ptSize (PBL.stdS S P) + m = i := by unfold PBL.stdS; rw [ptSize_toStd']; exact hP
  have hszQ : D.ptSize (PBL.stdS S Q) + m = i := by unfold PBL.stdS; rw [ptSize_toStd']; exact hQ
  have hRR : ContinuousOn (fun cc : ℂ × ℂ => (p v).RR (PBASM.cutSeq S p f χ n v ε) i a
      (PBL.stdS S P ++ [(m, cc.1)]) (PBL.stdS S Q ++ [(m, cc.2)])) (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)) := by
    rcases Nat.lt_or_ge i (S.G.r + 1) with hlt | hge
    · have hi' : i ≤ (D.parOf S v).r := by show i ≤ S.G.r; omega
      rw [hFn ε]
      refine rrBelow_cont (D.parOf S v) (p v) χ ε hn i hi' a S.Ntop hlen (PBL.stdS S P) (PBL.stdS S Q) m hm
        hszP hszQ ?_ ?_
      · intro hh t0 ht0
        obtain ⟨ε', hε', H⟩ := hSQ Cs le_rfl (D.parOf S v).k (D.parOf S v).r (Wp (S.pl v)) (Wq (S.pl v)) (p v).T χ
          (A₀ - 1) S.Ntop (D.parOf S v) rfl rfl hk2 hcut hA' ε hε i hi' a hlen (PBL.stdS S P) m
          (hc_app _ m hszP) hh hm hszP t0 ht0
        exact ⟨ε', hε', fun e => H e hn (bf + Kp * bf) hns hnC⟩
      · intro hh t0 ht0
        obtain ⟨ε', hε', H⟩ := hSQ Cs le_rfl (D.parOf S v).k (D.parOf S v).r (Wp (S.pl v)) (Wq (S.pl v)) (p v).T χ
          (A₀ - 1) S.Ntop (D.parOf S v) rfl rfl hk2 hcut hA' ε hε i hi' a hlen (PBL.stdS S Q) m
          (hc_app _ m hszQ) hh hm hszQ t0 ht0
        exact ⟨ε', hε', fun e => H e hn (bf + Kp * bf) hns hnC⟩
    · have hi1 : i = S.G.r + 1 := by omega
      subst hi1
      exact rrTop_cont (D.parOf S v) (p v) _ (hcpt ε hε) Cb (by rw [hl0]; exact hInD) a hcw (PBL.stdS S P)
        (PBL.stdS S Q) m hm hszP hszQ

  have hg0 : (0 : ℝ) < (S.g : ℝ) / (2 * Real.pi) := div_pos hgpos (by positivity)
  set lP : ℂ := ((((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + D.ptSize P : ℕ) : ℤ) (m : ℤ) : ℝ) : ℂ) *
    Complex.I ^ (m - 1) with hlP
  set lQ : ℂ := ((((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + D.ptSize Q : ℕ) : ℤ) (m : ℤ) : ℝ) : ℂ) *
    Complex.I ^ (m - 1) with hlQ
  have hlP0 : lP ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr (zpow_pos hg0 _).ne') (pow_ne_zero _ Complex.I_ne_zero)
  have hlQ0 : lQ ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr (zpow_pos hg0 _).ne') (pow_ne_zero _ Complex.I_ne_zero)
  have eP : ∀ c : ℂ, PBL.stdS S (P ++ [(m, c)]) = PBL.stdS S P ++ [(m, lP * c)] := fun c =>
    PBL.toStd_append_blkT _ _ _ _ _ _
  have eQ : ∀ c : ℂ, PBL.stdS S (Q ++ [(m, c)]) = PBL.stdS S Q ++ [(m, lQ * c)] := fun c =>
    PBL.toStd_append_blkT _ _ _ _ _ _
  have hgN : ∀ cc : ℂ × ℂ, KB.gN (PBL.setC S p (PBASM.cutSeq S p f χ n)) v ε i a (P ++ [(m, cc.1)]) (Q ++ [(m, cc.2)]) =
      (((√(PBL.nnS S (P ++ [(m, cc.1)])) * √(PBL.nnS S (Q ++ [(m, cc.2)])) : ℝ) : ℂ) *
        ((1 / (PBL.bS S (P ++ [(m, 1)]) * PBL.bS S (Q ++ [(m, 1)]) * PBL.ΓS S i) : ℝ) : ℂ) *
        (p v).RR (PBASM.cutSeq S p f χ n v ε) i a (PBL.stdS S P ++ [(m, lP * cc.1)])
          (PBL.stdS S Q ++ [(m, lQ * cc.2)])) /
        ((PBL.setC S p (PBASM.cutSeq S p f χ n)).sizeAt v a : ℂ) := by
    intro cc
    unfold KB.gN
    erw [PBL.gramLoc_setC hB]
    rw [bS_app S P m cc.1, bS_app S Q m cc.2, eP, eQ]
  refine ContinuousOn.congr ?_ (fun cc _ => hgN cc)
  refine ContinuousOn.div_const ?_ _
  refine ContinuousOn.mul (ContinuousOn.mul ?_ continuousOn_const) ?_
  · have e1 : ContinuousOn (fun cc : ℂ × ℂ => PBL.nnS S (P ++ [(m, cc.1)])) (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)) :=
      (nnS_cont S P m).comp continuousOn_fst (fun cc hcc => hcc.1)
    have e2 : ContinuousOn (fun cc : ℂ × ℂ => PBL.nnS S (Q ++ [(m, cc.2)])) (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)) :=
      (nnS_cont S Q m).comp continuousOn_snd (fun cc hcc => hcc.2)
    exact Complex.continuous_ofReal.comp_continuousOn
      ((Real.continuous_sqrt.comp_continuousOn e1).mul (Real.continuous_sqrt.comp_continuousOn e2))
  · have hmap : Set.MapsTo (fun cc : ℂ × ℂ => (lP * cc.1, lQ * cc.2)) (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ))
        (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)) := fun cc hcc => ⟨mul_ne_zero hlP0 hcc.1, mul_ne_zero hlQ0 hcc.2⟩
    exact hRR.comp (f := fun cc : ℂ × ℂ => (lP * cc.1, lQ * cc.2)) (Continuous.continuousOn (by fun_prop)) hmap

end final

end Formalism.FourierDecayAlt.P.LastBlockContinuity

theorem Formalism.FourierDecayAlt.P.kernel_continuity_built : Formalism.FourierDecayAlt.P.GermFibreKernels.KerContB := Formalism.FourierDecayAlt.P.LastBlockContinuity.level_forms_joint_continuity
