import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinLeTruncatedExponential
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadContinuityAtZeroOfStandard
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularityAtPlaceOfSubadditive
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OnePointBasisFundamentalDomainVolume
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardPairingOfHeads
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadGermSmoothExtension
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialExhaustion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FormZeroEqSlotPairingOfLe
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbFormPos
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorIsomorphismLevels
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGWaveMain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGDegLift
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal

noncomputable section

theorem cptCoef_cutF {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    {χ : ℝ → ℝ} (hχ : C6.IsCut0 χ) {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F) (ε : ℝ) :
    KB.CptCoef Bs (D.cutF Bs χ F ε) := by
  refine ⟨Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF Bs hχ hF.1 ε, ?_, ?_⟩
  · obtain ⟨R, hR⟩ := hF.2.1
    exact ⟨R, fun g hg hne => hR g hg (fun h0 => hne (by simp [D.cutF, h0]))⟩
  · obtain ⟨e, he, hge⟩ := hF.2.2
    exact ⟨e, he, fun g hg hne => hge g hg (fun h0 => hne (by simp [D.cutF, h0]))⟩

theorem isBoundedBilinearMap_compR {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] :
    IsBoundedBilinearMap ℝ (fun q : (Wq →L[ℂ] Wp) × (Wq →L[ℂ] Wq) => q.1.comp q.2) where
  add_left x₁ x₂ y := ContinuousLinearMap.add_comp x₁ x₂ y
  smul_left c x y := by ext v; simp
  add_right x y₁ y₂ := ContinuousLinearMap.comp_add x y₁ y₂
  smul_right c x y := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, smul_apply]
    exact ContinuousLinearMap.map_smul_of_tower x c (y v)
  bound := ⟨1, one_pos, fun x y => by simpa using ContinuousLinearMap.opNorm_comp_le x y⟩

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem ckOn_comp {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {f : B.Mat k r → (Wq →L[ℂ] Wp)}
    {A : B.Mat k r → (Wq →L[ℂ] Wq)} (hf : B.CkOn ⊤ (B.GV k r) f) (hA : B.CkOn ⊤ (B.GV k r) A) :
    B.CkOn ⊤ (B.GV k r) (fun g => (f g).comp (A g)) := by
  intro g₀ hg₀
  obtain ⟨U1, f1, hU1, h1, hc1, he1⟩ := hf g₀ hg₀
  obtain ⟨U2, A1, hU2, h2, hc2, he2⟩ := hA g₀ hg₀
  refine ⟨U1 ∩ U2, fun g => (f1 g).comp (A1 g), hU1.inter hU2, ⟨h1, h2⟩, ?_, ?_⟩
  · exact isBoundedBilinearMap_compR.contDiff.comp_contDiffOn
      ((hc1.mono Set.inter_subset_left).prodMk (hc2.mono Set.inter_subset_right))
  · intro x hx hxG
    simp only [he1 x hx.1 hxG, he2 x hx.2 hxG]

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

section fpm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem cptCoef_fpm (p : KB.Pl P Wp Wq) {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {A : B.Mat P.k P.r → (Wq →L[ℂ] Wq)}
    (p₀ : ℕ) (hf : KB.CptCoef p.T.base f) (hfA : B.CkOn ⊤ (B.GV P.k P.r) fun g => (f g).comp (A g)) :
    KB.CptCoef p.T.base (TBBx4.fpm p f A p₀) := by
  have ha : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun g : B.Mat P.k P.r => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf _ _).pow p₀)
  have hne : ∀ g, TBBx4.fpm p f A p₀ g ≠ 0 → f g ≠ 0 := by
    intro g hg h0
    apply hg
    simp [TBBx4.fpm, h0]
  refine ⟨PI.UnitaryCorollaryDerivatives.cC_smul_ck ha hfA, ?_, ?_⟩
  · obtain ⟨R, hR⟩ := hf.2.1
    exact ⟨R, fun g hg hne' => hR g hg (hne g hne')⟩
  · obtain ⟨e, he, hge⟩ := hf.2.2
    exact ⟨e, he, fun g hg hne' => hge g hg (hne g hne')⟩

theorem cptCoef_fpm_of (p : KB.Pl P Wp Wq) {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {A : B.Mat P.k P.r → (Wq →L[ℂ] Wq)}
    (p₀ : ℕ) (hf : KB.CptCoef p.T.base f) (hA : B.CkOn ⊤ (B.GV P.k P.r) A) :
    KB.CptCoef p.T.base (TBBx4.fpm p f A p₀) := by
  exact cptCoef_fpm p p₀ hf (ckOn_comp hf.1 hA)

end fpm

theorem posAt_of_cpt (hA : P5.ThmPActual) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Y : Finset ℝ) (N : ℕ) (hnn : ∀ y, 0 ≤ nn y) (hF : KB.CptCoef p.T.base F) : TBB.PosAt p nn F Y N := by
  refine Formalism.FourierDecayAlt.P.TBBx3.posAt_of_forms p nn F Y N hnn ?_
  intro j w h hj hw _
  by_cases hh : D.IsLocPt h j
  · rw [PBL.rr_eq_form p F j hj w h h hh hh]
    obtain ⟨ε, hε, hnv⟩ := PBL.slv_nv p hF j hj w h hh
    exact Formalism.FourierDecayAlt.P.TBBx5.form_re_nonneg p
      (Formalism.FourierDecayAlt.P.TBBx5.formNonneg_of hA (Formalism.FourierDecayAlt.P.pb_formPos : PBL.FormPos) p) j hj w hw.1 hε _ hnv
  · unfold KB.Pl.RR D.RRplace
    rw [dif_neg (fun h1 => hh h1.1)]
    simp

def GermCut (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ)
    (K N : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → TBBx5.GermAt p nn (D.cutF p.T.base χ F ε) Y K N

def LimE (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ)
    (N : ℕ) : Prop :=
  ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ∃ sz : ℝ, 0 ≤ sz ∧ sz ≤ TBB.normC nn w ∧
    Tendsto (fun ε : ℝ => (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re) (𝓝[>] 0)
      (𝓝 (sz * (B.beta p.T.base F F).re))

def LemB (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (κ₀ : ℝ) : Prop :=
  ENNReal.ofReal (B.beta p.T.base F F).re ≤ ENNReal.ofReal κ₀ * TBB.jN2 p F

def Amaps (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Ap Am : B.Mat P.k P.r → (Wq →L[ℂ] Wq))
    (ApPt AmPt : C.LPt → (Wq →L[ℂ] Wq)) (b : ℝ) (n₀ : ℕ) : Prop :=
  (∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ →
      p.V (fun g => (f g).comp (Ap g)) γ = (p.V f γ).comp (ApPt γ)) ∧
  (∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ →
      p.V (fun g => (f g).comp (Am g)) γ = (p.V f γ).comp (AmPt γ)) ∧
  (∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ → ∀ v : Wq,
      ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (TBB.Tq p / TBB.Gp p γ) ^ n₀ *
        (‖(ContinuousLinearMap.adjoint (ApPt γ)) v‖ ^ 2 + ‖(ContinuousLinearMap.adjoint (AmPt γ)) v‖ ^ 2)) ∧
  (∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ → ‖ApPt γ‖ ^ 2 ≤ (TBB.Gp p γ / TBB.Tq p) ^ n₀) ∧
  (∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ → ‖AmPt γ‖ ^ 2 ≤ (TBB.Gp p γ / TBB.Tq p) ^ n₀)

def BigCellDerivativeExpansion (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ : ℝ) (a₁ : ℕ) : Prop :=
  ∀ a, a ≤ a₁ → ∃ (n : ℕ) (fi : Fin n → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (co : Fin n → ℂ),
    ∑ i, ‖co i‖ ≤ b ^ (C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * (a : ℝ)) ∧
    (∀ i, TBB.jN2 p (fi i) ≤ TBB.jN2 p f) ∧
    (∀ i, AEMeasurable fun c : Fin (P.r + 1) → ℂ =>
      ENNReal.ofReal (TBB.Ew p (fun _ => 1) (fi i) (P.r + 1) [] (TBB.bigPt P.r c))) ∧
    ∀ c : Fin (P.r + 1) → ℂ, D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) →
      ((D.ptMatN (TBB.bigPt P.r c) (P.r + 1)).det ^ a) • p.V f (TBB.bigPt P.r c) =
        ∑ i, co i • p.V (fi i) (TBB.bigPt P.r c)

end place

theorem thmBpAt_of_leaves (hA : P5.ThmPActual) (C₃ CΛ C₀ Cκ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ)
    (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Ap Am : B.Mat P.k P.r → (Wq →L[ℂ] Wq))
      (ApPt AmPt : C.LPt → (Wq →L[ℂ] Wq)) (b Λ κ₀ : ℝ) (n₀ p₀ : ℕ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ)
      (Cb : ℝ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 0 < κ₀ →
      κ₀ ≤ b ^ (Cκ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2) → 1 ≤ TBB.Tq p →
      n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base f →
      B.CkOn ⊤ (B.GV P.k P.r) Ap → B.CkOn ⊤ (B.GV P.k P.r) Am →
      Amaps p f Ap Am ApPt AmPt b n₀ → BigCellDerivativeExpansion p f b C₃ (2 * p₀ + n₀) →
      TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N →
      GermCut p nn χ (TBBx4.fpm p f Ap p₀) Y K N → GermCut p nn χ (TBBx4.fpm p f Am p₀) Y K N →
      LimE p nn χ (TBBx4.fpm p f Ap p₀) Y N → LimE p nn χ (TBBx4.fpm p f Am p₀) Y N →
      LemB p (TBBx4.fpm p f Ap p₀) κ₀ → LemB p (TBBx4.fpm p f Am p₀) κ₀ →
      TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  obtain ⟨C₂, hC₂, hLS⟩ := Formalism.FourierDecayAlt.P.lemma_s_of_parts Formalism.FourierDecayAlt.P.lemma_s_induction_base
    Formalism.FourierDecayAlt.P.lemma_s_induction_up
  obtain ⟨C₄, hC₄⟩ := Formalism.FourierDecayAlt.P.theorem_b_of_parts C₃ CΛ C₀ C₂ Cκ hC₃ hCΛ hC₀ hC₂
  refine ⟨C₄, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f Ap Am ApPt AmPt b Λ κ₀ n₀ p₀ χ nn Y K N Cb hb hΛ hΛb hκ hκb hT hn₀ hp₀ hK hKN hχ
    hnn hCb hf hfAp hfAm hAm hexp hWG hLG hGp hGm hEp hEm hBp hBm
  have hPS : KB.PStd := Formalism.FourierDecayAlt.P.standard_pairing_of_heads Formalism.FourierDecayAlt.P.radial_head Formalism.FourierDecayAlt.P.head_top
  have hPt : ∀ F : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef p.T.base F → GermCut p nn χ F Y K N →
      LimE p nn χ F Y N → LemB p F κ₀ → TBB.PtBound p F (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1)) := by
    intro F hF hG hE hB
    refine Formalism.FourierDecayAlt.P.point_bound_of_corollary_s Wp Wq P p nn χ F Y Λ K N C₂ κ₀ hC₂.le hκ hnn
      ⟨1, one_pos, fun ε hε _ => ?_⟩ (Formalism.FourierDecayAlt.P.vector_truncation_at_place p χ F hχ.2.2)
      (Formalism.FourierDecayAlt.P.limit_zero_at_place p nn χ F Y N κ₀ hE hB)
    have hGc : KB.CptCoef p.T.base (D.cutF p.T.base χ F ε) := cptCoef_cutF p.T.base hχ hF ε
    have hPos : TBB.PosAt p nn (D.cutF p.T.base χ F ε) Y N :=
      posAt_of_cpt hA p nn _ Y N (fun y => (hnn y).le) hGc
    have hI2 := Formalism.FourierDecayAlt.P.head_continuity_at_zero_of_compact_coefficients hPS hA p nn _ Y N Cb hCb hGc
    have hI3 := Formalism.FourierDecayAlt.P.integral_three_at_place hA hPS Formalism.FourierDecayAlt.P.vector_isomorphism_levels Formalism.FourierDecayAlt.P.list_duality_level_group
      Formalism.FourierDecayAlt.P.degree_of_plane_wave (Formalism.FourierDecayAlt.P.pb_formPos : PBL.FormPos) p nn _ Y Λ K N Cb hCb hGc hnn hWG
    have hI4 := Formalism.FourierDecayAlt.P.integral_four_at_place hA Formalism.FourierDecayAlt.P.list_duality_level_group Formalism.FourierDecayAlt.P.degree_of_lift_pairing
      (Formalism.FourierDecayAlt.P.pb_formPos : PBL.FormPos) p nn _ Y Λ K N hGc hnn hLG
    have hI5 := Formalism.FourierDecayAlt.P.integral_five_at_place p nn _ Y K N hPos (hG ε hε)
    exact Formalism.FourierDecayAlt.P.corSOfLemmaS_statement Wp Wq P p nn _ Y Λ K N C₂ hKN hC₂.le hPos
      (hLS Wp Wq P p nn _ Y Λ K N hK hΛ hPos hI2 hI3 hI4 hI5)
  obtain ⟨h1, h2, h3, h4, h5⟩ := hAm
  have hNorm := Formalism.FourierDecayAlt.P.norm_bound_at_place p f Ap Am ApPt AmPt b n₀ p₀ h1 h2 h3 h4 h5
  have hReg := Formalism.FourierDecayAlt.P.regularity_at_place p f b C₃ (2 * p₀ + n₀) (by linarith) hexp
  exact hC₄ Wp Wq P p f _ _ b Λ κ₀ n₀ p₀ hb hΛ hΛb hκ hκb hT hn₀ hp₀ hNorm
    (hPt _ (cptCoef_fpm_of p p₀ hf hfAp) hGp hEp hBp) (hPt _ (cptCoef_fpm_of p p₀ hf hfAm) hGm hEm hBm) hReg

end

end Formalism.FourierDecayAlt.P.CutBP
