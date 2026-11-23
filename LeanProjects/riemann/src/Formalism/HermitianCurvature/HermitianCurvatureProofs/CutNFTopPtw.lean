import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LimitOfModuleForms
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCap

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section vec

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem vecV_congr_gt (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (q : C.LPt)
    {H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)} (δ : ℝ)
    (h : ∀ g ∈ B.GV k r, δ < Gf k r Bs.z Bs.z' g → H₁ g = H₂ g)
    (hq : ¬ (0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q) ∨ δ < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q) :
    D.vecV Bs ν' m₀ H₁ q = D.vecV Bs ν' m₀ H₂ q := by
  unfold D.vecV
  by_cases hq' : D.IsLocPt q (r + 1) ∧ 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q
  · simp only [dif_pos hq']
    have hδ : δ < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q := hq.resolve_left (not_not.2 hq'.2)
    by_cases h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN q (r + 1) ∧ D.IsDFrame Bs ν' m₀ γ
    · simp only [dif_pos h']
      have hγ := h'.choose_spec.1
      have hGq := Formalism.FourierDecayAlt.P.ptG_spec k r Bs.z Bs.z' q h'.choose hq'.1 h'.choose_spec.2.1
      have hpos : δ < Gf k r Bs.z Bs.z' h'.choose := hGq ▸ hδ
      have e := Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_smul_of_ae Bs h'.choose
        (D.muR Bs h'.choose (hq'.1.2 ▸ D.ptPerm q)) H₁ H₂ 1 (by
        filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
        simp only [D.orbIntegrand, B.rho, one_smul]
        rw [h _ (Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ) (by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp]; exact hpos)])
      rw [e, one_smul]
    · simp only [dif_neg h']
  · simp only [dif_neg hq']

end vec

section lift

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem theta_cutF_gt (p : KB.Pl P Wp Wq) {Cb : ℝ} (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) {χ : ℝ → ℝ}
    (hχ : C6.IsCut0 χ) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : B.CkOn ⊤ (B.GV P.k P.r) F) {ε : ℝ} (hε : 0 < ε)
    {w : List C.Letter} (hw : KB.CutWord P p.l0 w) (e : Wd.Ix (Fin w.length)) :
    ∀ g ∈ B.GV P.k P.r, ε < Gf P.k P.r p.T.base.z p.T.base.z' g →
      p.Θ.Θ w e (D.cutF p.T.base χ F ε) g = p.Θ.Θ w e F g := by
  intro g hg hgε
  obtain ⟨nf, fib, o, κ, Dop, -, hIn, -, -, hΘ⟩ := hCb w hw e
  have hdom : g ∈ C6.domL p.T.base ∅ := ⟨hg, lt_trans hε hgε, fun l hl => by simp at hl⟩
  rw [hΘ _ g hdom, hΘ _ g hdom]
  have hlen : ∀ T ∈ Dop, T.word.length ≤ o := by
    intro T hT
    obtain ⟨_, _, _, _, _, _, _, hl, _⟩ := hIn.2.2 T hT
    omega
  have hc : B.CkOn ⊤ (B.GV P.k P.r) (D.cutF p.T.base χ F ε) := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hF ε
  have hsub := Formalism.FourierDecayAlt.P.PBE.opApply_subGV Dop hlen (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hc)
    (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hF) g hg
  have hGc : Continuous (fun g : B.Mat P.k P.r => Gf P.k P.r p.T.base.z p.T.base.z' g) :=
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf p.T.base.z p.T.base.z').continuous
  have hU : IsOpen {x : B.Mat P.k P.r | ε < Gf P.k P.r p.T.base.z p.T.base.z' x} := isOpen_lt continuous_const hGc
  have h0 := Formalism.FourierDecayAlt.P.PBE.opApply_zero_near Dop (F := D.cutF p.T.base χ F ε - F) hU (by
    intro x _ hx
    replace hx : ε < Gf P.k P.r p.T.base.z p.T.base.z' x := hx
    have h1 : 1 ≤ Gf P.k P.r p.T.base.z p.T.base.z' x / ε := by rw [le_div_iff₀ hε]; linarith
    simp only [Pi.sub_apply, D.cutF, hχ.2.2 _ h1, Complex.ofReal_one, one_smul, sub_self]) g hg hgε
  rw [hsub] at h0
  exact sub_eq_zero.1 h0

end lift

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem rrTop_cutF_eq (p : KB.Pl P Wp Wq) {Cb : ℝ} (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) {χ : ℝ → ℝ}
    (hχ : C6.IsCut0 χ) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : B.CkOn ⊤ (B.GV P.k P.r) F) {ε : ℝ} (hε : 0 < ε)
    {w : List C.Letter} (hw : KB.CutWord P p.l0 w) (γ : C.LPt)
    (hγ : ¬ (0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r γ) ∨
      ε < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r γ) :
    p.RR (D.cutF p.T.base χ F ε) (P.r + 1) w γ γ = p.RR F (P.r + 1) w γ γ := by
  have hV : ∀ H₁ H₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp),
      (∀ g ∈ B.GV P.k P.r, ε < Gf P.k P.r p.T.base.z p.T.base.z' g → H₁ g = H₂ g) →
      D.vecV p.T.base p.ν' p.m₀ H₁ γ = D.vecV p.T.base p.ν' p.m₀ H₂ γ :=
    fun H₁ H₂ h => vecV_congr_gt p.T.base p.ν' p.m₀ γ ε h hγ
  have hcut : ∀ g ∈ B.GV P.k P.r, ε < Gf P.k P.r p.T.base.z p.T.base.z' g → D.cutF p.T.base χ F ε g = F g := by
    intro g _ hg
    have h1 : 1 ≤ Gf P.k P.r p.T.base.z p.T.base.z' g / ε := by rw [le_div_iff₀ hε]; linarith
    simp only [D.cutF, hχ.2.2 _ h1, Complex.ofReal_one, one_smul]
  unfold KB.Pl.RR D.RRplace
  by_cases h1 : D.IsLocPt γ (P.r + 1) ∧ D.IsLocPt γ (P.r + 1)
  · rw [dif_pos h1, dif_pos h1, dif_neg (by omega), dif_neg (by omega), if_pos rfl, if_pos rfl]
    by_cases h3 : w = []
    · rw [if_pos h3, if_pos h3, hV _ _ hcut]
    · rw [if_neg h3, if_neg h3]
      unfold Top.topOf
      refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun ρ _ => ?_
      rw [hV _ _ (theta_cutF_gt p hCb hχ hF hε hw e)]
  · rw [dif_neg h1, dif_neg h1]

theorem nFTopPtw_of (p : KB.Pl P Wp Wq) {Cb : ℝ} (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) {χ : ℝ → ℝ}
    (hχ : C6.IsCut0 χ) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : B.CkOn ⊤ (B.GV P.k P.r) F)
    {w : List C.Letter} (hw : KB.CutWord P p.l0 w) :
    ∀ c : Fin (P.r + 1) → ℂ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), topD p (D.cutF p.T.base χ F ε) w c = topD p F w c := by
  intro c
  set γ := TBB.bigPt P.r c
  set Gγ := D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r γ with hGγ
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ (¬ (0 < Gγ) ∨ ε < Gγ) := by
    by_cases hG : 0 < Gγ
    · filter_upwards [Ioo_mem_nhdsGT hG] with ε hε
      exact ⟨hε.1, Or.inr hε.2⟩
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact ⟨hε, Or.inl hG⟩
  filter_upwards [hev] with ε hε
  unfold topD TBB.Ew TBB.NP
  rw [rrTop_cutF_eq p hCb hχ hF hε.1 hw γ hε.2]

end place

theorem top_pointwise_all_levels_holds : NFTopPtwAll := by
  intro Cb
  refine ⟨0, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw _
  obtain ⟨hχ, hCb, hf, -, -, -⟩ := hH
  have hF : B.CkOn ⊤ (B.GV P.k P.r) (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) :=
    ckOn_fpm p p₀ hf (Formalism.FourierDecayAlt.P.CutMP.ER.ckOn_const' _)
  exact Filter.Eventually.of_forall fun c => nFTopPtw_of p hCb hχ hF hw.1 c

end

end Formalism.FourierDecayAlt.P.CutBP
