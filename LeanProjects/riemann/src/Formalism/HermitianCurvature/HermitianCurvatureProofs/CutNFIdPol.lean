import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFId

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def midCut (χ' χ : ℝ → ℝ) : ℝ → ℝ := fun x => (χ' x + χ x) / 2

theorem isCut0_midCut {χ' χ : ℝ → ℝ} (h' : C6.IsCut0 χ') (h : C6.IsCut0 χ) : C6.IsCut0 (midCut χ' χ) := by
  obtain ⟨c1, ⟨d1, hd1, z1⟩, o1⟩ := h'
  obtain ⟨c2, ⟨d2, hd2, z2⟩, o2⟩ := h
  refine ⟨by unfold midCut; exact (c1.add c2).div_const 2, ⟨min d1 d2, lt_min hd1 hd2, fun x hx => ?_⟩, fun x hx => ?_⟩
  · simp only [midCut, z1 x (lt_of_lt_of_le hx (min_le_left _ _)), z2 x (lt_of_lt_of_le hx (min_le_right _ _))]
    norm_num
  · simp only [midCut, o1 x hx, o2 x hx]
    norm_num

def NFPolQuadAll : Prop :=
  P5.ThmPActual → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ∀ ε : ℝ, 0 < ε →
      Integrable (topD p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w) ∧
      (pair0 p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε)
        (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w).re =
        ∫ c, topD p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w c

def NFPairMidAll : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ χ' : ℝ → ℝ, C6.IsCut0 χ' → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
      ∀ ε : ℝ, 0 < ε →
        (pair0 p (D.cutF p.T.base (midCut χ' χ) (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε)
          (D.cutF p.T.base (midCut χ' χ) (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w).re =
        (pair0 p (D.cutF p.T.base χ' (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε)
          (D.cutF p.T.base χ' (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w).re / 4 +
        (pair0 p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε)
          (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w).re / 4 +
        (pair0 p (D.cutF p.T.base χ' (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε)
          (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w).re / 2

def NFTopMidAll : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ χ' : ℝ → ℝ, C6.IsCut0 χ' → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
      ∀ ε : ℝ, 0 < ε → ∀ c : Fin (P.r + 1) → ℂ,
        topD p (D.cutF p.T.base (midCut χ' χ) (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w c =
        topD p (D.cutF p.T.base χ' (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w c / 4 +
        topD p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w c / 4 +
        topPD p (D.cutF p.T.base χ' (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε)
          (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w c / 2

theorem nfPolFormAll_of (s1 : NFPolQuadAll) (s2 : NFPairMidAll) (s3 : NFTopMidAll) : NFPolFormAll := by
  intro hA Cb
  obtain ⟨C1, H1⟩ := s1 hA Cb
  obtain ⟨C2, H2⟩ := s2 Cb
  obtain ⟨C3, H3⟩ := s3 Cb
  refine ⟨max C1 (max C2 C3), ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH χ' hχ' w hw hN ε hε
  have m1 : C1 ≤ max C1 (max C2 C3) := le_max_left _ _
  have m2 : C2 ≤ max C1 (max C2 C3) := le_max_of_le_right (le_max_left _ _)
  have m3 : C3 ≤ max C1 (max C2 C3) := le_max_of_le_right (le_max_right _ _)
  have hχ : C6.IsCut0 χ := hH.1
  have hm := isCut0_midCut hχ' hχ
  set F' := TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀ with hF'
  obtain ⟨iu, qu⟩ := H1 Wp Wq P p f A₀ p₀ χ' Y N (nfHyp_mono hH m1 hχ') w hw hN ε hε
  obtain ⟨iv, qv⟩ := H1 Wp Wq P p f A₀ p₀ χ Y N (nfHyp_mono hH m1 hχ) w hw hN ε hε
  obtain ⟨im, qm⟩ := H1 Wp Wq P p f A₀ p₀ (midCut χ' χ) Y N (nfHyp_mono hH m1 hm) w hw hN ε hε
  have hpair := H2 Wp Wq P p f A₀ p₀ χ Y N (nfHyp_mono hH m2 hχ) χ' hχ' w hw hN ε hε
  have htop := H3 Wp Wq P p f A₀ p₀ χ Y N (nfHyp_mono hH m3 hχ) χ' hχ' w hw hN ε hε
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

end

end Formalism.FourierDecayAlt.P.CutBP
