import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFHypS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFIdPolAll
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFIdPairPtw
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFIdBetaLim
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopFormDone

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem nfHypS_mono {Cb c c' : ℝ} {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    {p : KB.Pl P Wp Wq} {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {A₀ : ℝ} {p₀ : ℕ} {χ χ' : ℝ → ℝ} {N : ℕ}
    (h : NFHypS Cb c p f A₀ p₀ χ N) (hc : c' ≤ c) (hχ' : C6.IsCut0 χ') : NFHypS Cb c' p f A₀ p₀ χ' N :=
  ⟨nfHyp_mono h.1 hc hχ', h.2.1, h.2.2⟩

def NFPolQuadAllS : Prop :=
  P5.ThmPActual → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHypS Cb Cc p f A₀ p₀ χ N → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ∀ ε : ℝ, 0 < ε →
      Integrable (topD p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w) ∧
      (pair0 p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε)
        (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w).re =
        ∫ c, topD p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w c

def NFPolFormAllS : Prop :=
  P5.ThmPActual → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHypS Cb Cc p f A₀ p₀ χ N → ∀ χ' : ℝ → ℝ, C6.IsCut0 χ' → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
      ∀ ε : ℝ, 0 < ε →
        Integrable (topPD p (D.cutF p.T.base χ' (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε)
          (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w) ∧
        (pair0 p (D.cutF p.T.base χ' (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε)
          (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w).re =
          ∫ c, topPD p (D.cutF p.T.base χ' (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε)
            (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w c

theorem nFTopFormAllS_of (hMeas : TopDMeasCpt) (hApx : NFApxDomAllS) : NFTopFormAllS := by
  intro hA Cb
  obtain ⟨C1, H1⟩ := Formalism.FourierDecayAlt.P.limit_of_module_forms Cb
  obtain ⟨C2, H2⟩ := hApx Cb
  refine ⟨max C1 C2, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN ε hε
  have hH1 := nfHyp_monoC hH.1 (le_max_left C1 C2)
  have hH2 := nfHypS_monoC hH (le_max_right C1 C2)
  obtain ⟨hχ, hCb, hf, hfA, hthr, -⟩ := hH1
  set F' := TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀ with hF'
  have hF'ck : B.CkOn ⊤ (B.GV P.k P.r) F' := by
    rw [hF', fpm_id]
    exact ckOn_Gpow_smul _ _ p₀ hf
  obtain ⟨hcpt, hlim⟩ := H1 Wp Wq P p F' χ ε (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ)) N (cutN P.k P.r) hCb hχ hε
    hF'ck (inCC_fpm_id p p₀ hfA) hthr (fun _ _ => rfl)
  set H := D.cutF p.T.base χ F' ε with hHdef
  have hcpt' : ∀ n, KB.CptCoef p.T.base (apx H n) := hcpt
  have hform : ∀ n, (p.RR (apx H n) 0 w [] []).re = ∫ c, topD p (apx H n) w c := fun n =>
    normal_form_compact_support_holds hA Wp Wq P p (apx H n) Y w Cb hCb (hcpt' n) hw
      (hMeas Wp Wq P p (apx H n) w Cb hCb (hcpt' n) hw.1)
  have hlim0 : Tendsto (fun n => ∫ c, topD p (apx H n) w c) atTop (𝓝 (p.RR H 0 w [] []).re) := by
    have := (Complex.continuous_re.tendsto _).comp (hlim 0 w hw.1 hN [] [])
    refine this.congr fun n => ?_
    exact hform n
  have hptw : ∀ c, Tendsto (fun n => topD p (apx H n) w c) atTop (𝓝 (topD p H w c)) := by
    intro c
    unfold topD TBB.Ew TBB.NP
    exact (Complex.continuous_re.tendsto _).comp
      (tendsto_const_nhds.mul (hlim (P.r + 1) w hw.1 hN (TBB.bigPt P.r c) (TBB.bigPt P.r c)))
  obtain ⟨h, hint, hb⟩ := H2 Wp Wq P p f A₀ p₀ χ Y N hH2 w hw hN ε hε
  have hdct : Tendsto (fun n => ∫ c, topD p (apx H n) w c) atTop (𝓝 (∫ c, topD p H w c)) :=
    tendsto_integral_of_dominated_convergence h
      (fun n => hMeas Wp Wq P p (apx H n) w Cb hCb (hcpt' n) hw.1) hint hb
      (Filter.Eventually.of_forall hptw)
  exact tendsto_nhds_unique hlim0 hdct

theorem nFTopIntS_of (hMeas : TopDMeasCpt) (hApx : NFApxDomAllS) (Cb : ℝ) : ∃ Cc : ℝ,
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
      NFHypS Cb Cc p f A₀ p₀ χ N → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ∀ ε : ℝ, 0 < ε →
        Integrable (topD p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w) := by
  obtain ⟨C1, H1⟩ := Formalism.FourierDecayAlt.P.limit_of_module_forms Cb
  obtain ⟨C2, H2⟩ := hApx Cb
  refine ⟨max C1 C2, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN ε hε
  have hH1 := nfHyp_monoC hH.1 (le_max_left C1 C2)
  have hH2 := nfHypS_monoC hH (le_max_right C1 C2)
  obtain ⟨hχ, hCb, hf, hfA, hthr, -⟩ := hH1
  set F' := TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀ with hF'
  have hF'ck : B.CkOn ⊤ (B.GV P.k P.r) F' := by
    rw [hF', fpm_id]
    exact ckOn_Gpow_smul _ _ p₀ hf
  obtain ⟨hcpt, hlim⟩ := H1 Wp Wq P p F' χ ε (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ)) N (cutN P.k P.r) hCb hχ hε
    hF'ck (inCC_fpm_id p p₀ hfA) hthr (fun _ _ => rfl)
  set H := D.cutF p.T.base χ F' ε with hHdef
  have hcpt' : ∀ n, KB.CptCoef p.T.base (apx H n) := hcpt
  have hptw : ∀ c, Tendsto (fun n => topD p (apx H n) w c) atTop (𝓝 (topD p H w c)) := by
    intro c
    unfold topD TBB.Ew TBB.NP
    exact (Complex.continuous_re.tendsto _).comp
      (tendsto_const_nhds.mul (hlim (P.r + 1) w hw.1 hN (TBB.bigPt P.r c) (TBB.bigPt P.r c)))
  obtain ⟨h, hint, hb⟩ := H2 Wp Wq P p f A₀ p₀ χ Y N hH2 w hw hN ε hε
  have hm : AEStronglyMeasurable (topD p H w) volume :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => hMeas Wp Wq P p (apx H n) w Cb hCb (hcpt' n) hw.1) (Filter.Eventually.of_forall hptw)
  refine hint.mono' hm ?_
  have hb' : ∀ᵐ c, ∀ n, ‖topD p (apx H n) w c‖ ≤ h c := ae_all_iff.2 hb
  filter_upwards [hb'] with c hc
  exact le_of_tendsto' ((continuous_norm.tendsto _).comp (hptw c)) hc

theorem nfPolQuadAllS_of (hMeas : TopDMeasCpt) (hApx : NFApxDomAllS) : NFPolQuadAllS := by
  intro hA Cb
  obtain ⟨C1, H1⟩ := nFTopFormAllS_of hMeas hApx hA Cb
  obtain ⟨C2, H2⟩ := nFTopIntS_of hMeas hApx Cb
  refine ⟨max C1 C2, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN ε hε
  have hH1 := nfHypS_mono hH (le_max_left C1 C2) hH.1.1
  have hH2 := nfHypS_mono hH (le_max_right C1 C2) hH.1.1
  refine ⟨H2 Wp Wq P p f A₀ p₀ χ Y N hH2 w hw hN ε hε, ?_⟩
  have hid : B.CkOn ⊤ (B.GV P.k P.r) (fun _ : B.Mat P.k P.r => ContinuousLinearMap.id ℂ Wq) := fun g₀ _ =>
    ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ Wq, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  have hF := ckOn_fpm p p₀ hH.1.2.2.1 hid
  have hc := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hH.1.1 hF ε
  rw [← residual_pairing_eq_self_pairing p hc hw.1]
  exact H1 Wp Wq P p f A₀ p₀ χ Y N hH1 w hw hN ε hε

theorem nfPolFormAllS_of (s1 : NFPolQuadAllS) (s2 : NFPairMidAll) (s3 : NFTopMidAll) : NFPolFormAllS := by
  intro hA Cb
  obtain ⟨C1, H1⟩ := s1 hA Cb
  obtain ⟨C2, H2⟩ := s2 Cb
  obtain ⟨C3, H3⟩ := s3 Cb
  refine ⟨max C1 (max C2 C3), ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH χ' hχ' w hw hN ε hε
  have m1 : C1 ≤ max C1 (max C2 C3) := le_max_left _ _
  have m2 : C2 ≤ max C1 (max C2 C3) := le_max_of_le_right (le_max_left _ _)
  have m3 : C3 ≤ max C1 (max C2 C3) := le_max_of_le_right (le_max_right _ _)
  have hχ : C6.IsCut0 χ := hH.1.1
  have hm := isCut0_midCut hχ' hχ
  set F' := TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀ with hF'
  obtain ⟨iu, qu⟩ := H1 Wp Wq P p f A₀ p₀ χ' Y N (nfHypS_mono hH m1 hχ') w hw hN ε hε
  obtain ⟨iv, qv⟩ := H1 Wp Wq P p f A₀ p₀ χ Y N (nfHypS_mono hH m1 hχ) w hw hN ε hε
  obtain ⟨im, qm⟩ := H1 Wp Wq P p f A₀ p₀ (midCut χ' χ) Y N (nfHypS_mono hH m1 hm) w hw hN ε hε
  have hpair := H2 Wp Wq P p f A₀ p₀ χ Y N (nfHyp_mono hH.1 m2 hχ) χ' hχ' w hw hN ε hε
  have htop := H3 Wp Wq P p f A₀ p₀ χ Y N (nfHyp_mono hH.1 m3 hχ) χ' hχ' w hw hN ε hε
  have e : topPD p (D.cutF p.T.base χ' F' ε) (D.cutF p.T.base χ F' ε) w = fun c =>
      2 * topD p (D.cutF p.T.base (midCut χ' χ) F' ε) w c - topD p (D.cutF p.T.base χ' F' ε) w c / 2 -
        topD p (D.cutF p.T.base χ F' ε) w c / 2 := by
    funext c
    have := htop c
    linarith
  have hi1 : Integrable (fun c => 2 * topD p (D.cutF p.T.base (midCut χ' χ) F' ε) w c) := im.const_mul 2
  have hi2 : Integrable (fun c => topD p (D.cutF p.T.base χ' F' ε) w c / 2) := iu.div_const 2
  have hi3 : Integrable (fun c => topD p (D.cutF p.T.base χ F' ε) w c / 2) := iv.div_const 2
  refine ⟨?_, ?_⟩
  · rw [e]
    exact (hi1.sub hi2).sub hi3
  · have hi12 : Integrable (fun c => 2 * topD p (D.cutF p.T.base (midCut χ' χ) F' ε) w c -
        topD p (D.cutF p.T.base χ' F' ε) w c / 2) := hi1.sub hi2
    rw [e, integral_sub hi12 hi3, integral_sub hi1 hi2, integral_const_mul, integral_div, integral_div,
      ← qu, ← qv, ← qm, hpair]
    ring

theorem nfTopIdAllS_of (hA : P5.ThmPActual) (h3 : NFTopDomAllS) (s1 : NFPolFormAllS) (s2 : NFPairPtwAll)
    (s4 : NFBetaLimAll) : NFTopIdAllS := by
  intro Cb
  obtain ⟨C1, H1⟩ := s1 hA Cb
  obtain ⟨C2, H2⟩ := s2 Cb
  obtain ⟨C3, H3⟩ := h3 Cb
  obtain ⟨C4, H4⟩ := s4 Cb
  refine ⟨max (max C1 C2) (max C3 C4), ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN
  have hχ : C6.IsCut0 χ := hH.1.1
  obtain ⟨δ, hδ, hχ0⟩ := hχ.2.1
  set κ : ℝ := min δ 1 / 2 with hκdef
  have hκ : 0 < κ := by positivity
  have hκ1 : κ ≤ 1 := by
    have : min δ 1 ≤ 1 := min_le_right _ _
    linarith
  have hκδ : κ < δ := by
    have : min δ 1 ≤ δ := min_le_left _ _
    linarith
  set χκ : ℝ → ℝ := fun x => χ (x / κ) with hχκdef
  have hχκ : C6.IsCut0 χκ := by
    refine ⟨hχ.1.comp (contDiff_id.div_const κ), ⟨κ * δ, mul_pos hκ hδ, fun x hx => hχ0 _ ?_⟩, fun x hx => hχ.2.2 _ ?_⟩
    · rw [div_lt_iff₀ hκ]
      linarith
    · rw [le_div_iff₀ hκ]
      linarith
  have hχκ1 : ∀ x, κ ≤ x → χκ x = 1 := fun x hx => hχ.2.2 _ ((le_div_iff₀ hκ).2 (by linarith))
  have hid : B.CkOn ⊤ (B.GV P.k P.r) (fun _ : B.Mat P.k P.r => ContinuousLinearMap.id ℂ Wq) := fun g₀ _ =>
    ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ Wq, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  have hF := ckOn_fpm p p₀ hH.1.2.2.1 hid
  set F' := TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀ with hF'
  have m1 : C1 ≤ max (max C1 C2) (max C3 C4) := le_max_of_le_left (le_max_left _ _)
  have m2 : C2 ≤ max (max C1 C2) (max C3 C4) := le_max_of_le_left (le_max_right _ _)
  have m3 : C3 ≤ max (max C1 C2) (max C3 C4) := le_max_of_le_right (le_max_left _ _)
  have m4 : C4 ≤ max (max C1 C2) (max C3 C4) := le_max_of_le_right (le_max_right _ _)

  have hβ : Tendsto (fun ε : ℝ => (pair0 p (D.cutF p.T.base χκ F' ε) (D.cutF p.T.base χ F' ε) w).re) (𝓝[>] 0)
      (𝓝 (pair0 p F' F' w).re) := by
    refine (H4 Wp Wq P p f A₀ p₀ χ Y N (nfHyp_mono hH.1 m4 hχ) w hw hN).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [pairing_truncation_locality p hF hχκ hκδ hχ0 hχκ1 w hε]

  obtain ⟨-, hA, hAi, hAb⟩ := H3 Wp Wq P p f A₀ p₀ χκ Y N (nfHypS_mono hH m3 hχκ) w hw hN
  obtain ⟨-, hB, hBi, hBb⟩ := H3 Wp Wq P p f A₀ p₀ χ Y N (nfHypS_mono hH m3 hχ) w hw hN
  have hT : Tendsto (fun ε : ℝ => ∫ c, topPD p (D.cutF p.T.base χκ F' ε) (D.cutF p.T.base χ F' ε) w c) (𝓝[>] 0)
      (𝓝 (∫ c, topD p F' w c)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun c => (hA c + hB c) / 2) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (H1 Wp Wq P p f A₀ p₀ χ Y N (nfHypS_mono hH m1 hχ) χκ hχκ w hw hN ε hε).1.aestronglyMeasurable
    · filter_upwards [hAb, hBb] with ε ha hb
      filter_upwards [ha, hb] with c hac hbc
      rw [Real.norm_eq_abs]
      refine (topPD_cs p _ _ w c).trans ?_
      have e1 := (le_abs_self (topD p (D.cutF p.T.base χκ F' ε) w c)).trans (le_of_eq (Real.norm_eq_abs _).symm)
      have e2 := (le_abs_self (topD p (D.cutF p.T.base χ F' ε) w c)).trans (le_of_eq (Real.norm_eq_abs _).symm)
      linarith
    · exact (hAi.add hBi).div_const 2
    · filter_upwards [H2 Wp Wq P p f A₀ p₀ χ Y N (nfHyp_mono hH.1 m2 hχ) χκ hχκ w hw hN] with c hc
      exact tendsto_const_nhds.congr' (hc.mono fun ε h => h.symm)
  have hE : (fun ε : ℝ => (pair0 p (D.cutF p.T.base χκ F' ε) (D.cutF p.T.base χ F' ε) w).re) =ᶠ[𝓝[>] (0 : ℝ)]
      fun ε => ∫ c, topPD p (D.cutF p.T.base χκ F' ε) (D.cutF p.T.base χ F' ε) w c := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (H1 Wp Wq P p f A₀ p₀ χ Y N (nfHypS_mono hH m1 hχ) χκ hχκ w hw hN ε hε).2
  have huniq := tendsto_nhds_unique (hβ.congr' hE) hT
  show ∫ c, topD p F' w c = (p.RR F' 0 w [] []).re
  rw [← huniq, residual_pairing_eq_self_pairing p hF hw.1]

end

end Formalism.FourierDecayAlt.P.CutBP
