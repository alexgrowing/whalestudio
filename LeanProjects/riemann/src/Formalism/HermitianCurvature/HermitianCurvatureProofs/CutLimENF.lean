import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_PtwCut

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def topD (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ) : ℝ :=
  TBB.Ew p (fun _ => 1) H (P.r + 1) w (TBB.bigPt P.r c)

def NFTopForm (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) : Prop :=
  ∀ ε : ℝ, 0 < ε → (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re = ∫ c, topD p (D.cutF p.T.base χ F ε) w c

def NFTopPtw (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) : Prop :=
  ∀ᵐ c : Fin (P.r + 1) → ℂ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), topD p (D.cutF p.T.base χ F ε) w c = topD p F w c

def NFTopDom (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) : Prop :=
  (∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (topD p (D.cutF p.T.base χ F ε) w) volume) ∧
  ∃ h : (Fin (P.r + 1) → ℂ) → ℝ, Integrable h ∧
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ c : Fin (P.r + 1) → ℂ, ‖topD p (D.cutF p.T.base χ F ε) w c‖ ≤ h c

def NFTopId (p : KB.Pl P Wp Wq) (_χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) : Prop :=
  ∫ c, topD p F w c = (p.RR F 0 w [] []).re

theorem limEvT_of_NF (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ)
    (hT : ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → NFTopForm p χ F w)
    (hP : ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → NFTopPtw p χ F w)
    (hD : ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → NFTopDom p χ F w)
    (hI : ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → NFTopId p χ F w) : LimEvT p χ F Y N := by
  intro w hw hl
  obtain ⟨hmeas, h, hint, hbd⟩ := hD w hw hl
  have hlim := MeasureTheory.tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (F := fun ε c => topD p (D.cutF p.T.base χ F ε) w c) (f := topD p F w) h hmeas hbd hint
    ((hP w hw hl).mono fun c hc => Filter.Tendsto.congr' (hc.mono fun ε he => he.symm) tendsto_const_nhds)
  rw [← hI w hw hl]
  refine Filter.Tendsto.congr' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hT w hw hl ε hε).symm

end place

def NFHyp (Cb Cc : ℝ) {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (N : ℕ) : Prop :=
  C6.IsCut0 χ ∧ KB.InDDplus2 P p.l0 p.T.base Cb p.Θ ∧ B.CkOn ⊤ (B.GV P.k P.r) f ∧ (∀ m : ℕ, B.InCC A₀ m f) ∧
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
      A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) ∧
    N ≤ 2 * p₀

def NFTopFormAll : Prop :=
  P5.ThmPActual → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
      NFTopForm p χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) w

def NFTopPtwAll : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
      NFTopPtw p χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) w

def NFTopDomAll : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
      NFTopDom p χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) w

def NFTopIdAll : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
      NFTopId p χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) w

theorem limEvT_fpm_of_NF (hA : P5.ThmPActual) (h1 : NFTopFormAll) (h2 : NFTopPtwAll) (h3 : NFTopDomAll) (h4 : NFTopIdAll) (Cb : ℝ) :
    ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
      NFHyp Cb Cc p f A₀ p₀ χ N →
      LimEvT p χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N := by
  obtain ⟨C1, k1⟩ := h1 hA Cb
  obtain ⟨C2, k2⟩ := h2 Cb
  obtain ⟨C3, k3⟩ := h3 Cb
  obtain ⟨C4, k4⟩ := h4 Cb
  refine ⟨max (max C1 C2) (max C3 C4), ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH
  have mono : ∀ C, C ≤ max (max C1 C2) (max C3 C4) → NFHyp Cb C p f A₀ p₀ χ N := by
    intro C hC
    unfold NFHyp at hH ⊢
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hH
    refine ⟨a1, a2, a3, a4, le_trans ?_ a5, a6⟩
    gcongr
  exact limEvT_of_NF p χ _ Y N (k1 Wp Wq P p f A₀ p₀ χ Y N (mono C1 (by simp))) (k2 Wp Wq P p f A₀ p₀ χ Y N (mono C2 (by simp)))
    (k3 Wp Wq P p f A₀ p₀ χ Y N (mono C3 (by simp))) (k4 Wp Wq P p f A₀ p₀ χ Y N (mono C4 (by simp)))

end

end Formalism.FourierDecayAlt.P.CutBP
