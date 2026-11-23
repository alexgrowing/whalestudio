import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_PtwCut

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

open Classical

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def topPair (p : KB.Pl P Wp Wq) (F₁ F₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (γ : C.LPt) : ℂ :=
  if w = [] then B.hsInner (p.V F₁ γ) (p.V F₂ γ) else
    ∑ e : Wd.Ix (Fin w.length), ∑ ρ : M.Ty P,
      ((Top.dH P p.l0 (TBB.TTp p) w γ e ρ * Top.dH P p.l0 (TBB.TTp p) w γ e ρ : ℝ) : ℂ) *
        B.hsInner ((p.TP.E ρ).comp (D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e F₁) γ))
          ((p.TP.E ρ).comp (D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e F₂) γ))

def topPD (p : KB.Pl P Wp Wq) (F₁ F₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter)
    (c : Fin (P.r + 1) → ℂ) : ℝ :=
  (((Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) *
      Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) : ℝ) : ℂ) *
    (if D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) then topPair p F₁ F₂ w (TBB.bigPt P.r c) else 0)).re

def pair0 (p : KB.Pl P Wp Wq) (F₁ F₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) : ℂ :=
  B.beta p.T.base (w.foldr (fun a H => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) H) F₁) F₂

theorem normC_one (w : List C.Letter) : TBB.normC (fun _ => (1 : ℝ)) w = 1 := by
  unfold TBB.normC
  induction w with
  | nil => simp
  | cons a w ih => simp [ih]

theorem topPD_self (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter)
    (c : Fin (P.r + 1) → ℂ) : topPD p F F w c = topD p F w c := by
  unfold topPD topD TBB.Ew TBB.NP
  rw [normC_one, div_one]
  congr 2
  unfold KB.Pl.RR D.RRplace
  by_cases hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1)
  · rw [if_pos hl, dif_pos ⟨hl, hl⟩, dif_neg (by omega), if_pos rfl]
    by_cases hw : w = []
    · subst hw
      simp [topPair, KB.Pl.V]
    · rw [if_neg hw]
      unfold topPair Top.topOf
      rw [if_neg hw]
      rfl
  · rw [if_neg hl, dif_neg (fun h => hl h.1)]

theorem residual_pairing_eq_self_pairing (p : KB.Pl P Wp Wq) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : B.CkOn ⊤ (B.GV P.k P.r) F)
    {w : List C.Letter} (hw : KB.CutWord P p.l0 w) : p.RR F 0 w [] [] = pair0 p F F w := by
  unfold KB.Pl.RR
  rw [Formalism.FourierDecayAlt.P.level_zero_holds _ _ _ _ _ _ _ _ _ _ _ hF (good_positioned_of_cut hw)]
  rfl

theorem hsInner_re_cs (x y : Wq →L[ℂ] Wp) :
    |(B.hsInner x y).re| ≤ ((B.hsInner x x).re + (B.hsInner y y).re) / 2 := by
  unfold B.hsInner
  have h1 : |(inner ℂ (B.hsVec y) (B.hsVec x)).re| ≤ ‖B.hsVec y‖ * ‖B.hsVec x‖ :=
    (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
  have hx : (inner ℂ (B.hsVec x) (B.hsVec x)).re = ‖B.hsVec x‖ ^ 2 := by
    have := inner_self_eq_norm_sq (𝕜 := ℂ) (B.hsVec x)
    simpa using this
  have hy : (inner ℂ (B.hsVec y) (B.hsVec y)).re = ‖B.hsVec y‖ ^ 2 := by
    have := inner_self_eq_norm_sq (𝕜 := ℂ) (B.hsVec y)
    simpa using this
  rw [hx, hy]
  nlinarith [sq_nonneg (‖B.hsVec y‖ - ‖B.hsVec x‖)]

theorem sum_abs_cs {ι : Type} (s : Finset ι) (a b c : ι → ℝ) (h : ∀ i ∈ s, |a i| ≤ (b i + c i) / 2) :
    |∑ i ∈ s, a i| ≤ (∑ i ∈ s, b i + ∑ i ∈ s, c i) / 2 := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  exact Finset.sum_le_sum h

theorem topPair_re_cs (p : KB.Pl P Wp Wq) (u v : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter)
    (γ : C.LPt) :
    |(topPair p u v w γ).re| ≤ ((topPair p u u w γ).re + (topPair p v v w γ).re) / 2 := by
  unfold topPair
  by_cases hw : w = []
  · simp only [if_pos hw]
    exact hsInner_re_cs _ _
  · simp only [if_neg hw, Complex.re_sum, Complex.re_ofReal_mul]
    refine sum_abs_cs _ _ _ _ fun e _ => ?_
    refine sum_abs_cs _ _ _ _ fun ρ _ => ?_
    have hd : 0 ≤ Top.dH P p.l0 (TBB.TTp p) w γ e ρ * Top.dH P p.l0 (TBB.TTp p) w γ e ρ := mul_self_nonneg _
    rw [abs_mul, abs_of_nonneg hd]
    have := hsInner_re_cs ((p.TP.E ρ).comp (D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e u) γ))
      ((p.TP.E ρ).comp (D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e v) γ))
    nlinarith

theorem topPD_cs (p : KB.Pl P Wp Wq) (u v : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter)
    (c : Fin (P.r + 1) → ℂ) : |topPD p u v w c| ≤ (topD p u w c + topD p v w c) / 2 := by
  rw [← topPD_self, ← topPD_self]
  unfold topPD
  have hs : 0 ≤ Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) *
      Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) := mul_self_nonneg _
  simp only [Complex.re_ofReal_mul]
  by_cases hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1)
  · simp only [if_pos hl]
    rw [abs_mul, abs_of_nonneg hs]
    have := topPair_re_cs p u v w (TBB.bigPt P.r c)
    nlinarith
  · simp [if_neg hl]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem pairing_truncation_locality (p : KB.Pl P Wp Wq) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : B.CkOn ⊤ (B.GV P.k P.r) F)
    {χ χ' : ℝ → ℝ} (hχ' : C6.IsCut0 χ') {δ₀ δ : ℝ} (hδ : δ₀ < δ) (h0 : ∀ x, x < δ → χ x = 0)
    (h1 : ∀ x, δ₀ ≤ x → χ' x = 1) (w : List C.Letter) {ε : ℝ} (hε : 0 < ε) :
    pair0 p (D.cutF p.T.base χ' F ε) (D.cutF p.T.base χ F ε) w = pair0 p F (D.cutF p.T.base χ F ε) w := by
  unfold pair0 B.beta betaBig
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  by_cases hq : bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q = 0
  · show (bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q : ℂ) * _ =
      (bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q : ℂ) * _
    rw [hq]
    simp
  obtain ⟨hgG, hpos⟩ := bigCell_pos p q hq
  set g := bigCell P.k P.r q.1 (p.T.base.μsec q.2) with hg
  show (bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q : ℂ) *
      inner ℂ (B.hsVec (B.JF p.T.base (D.cutF p.T.base χ F ε) g))
        (B.hsVec (B.JF p.T.base (w.foldr (fun a H => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) H)
          (D.cutF p.T.base χ' F ε)) g)) =
    (bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q : ℂ) *
      inner ℂ (B.hsVec (B.JF p.T.base (D.cutF p.T.base χ F ε) g))
        (B.hsVec (B.JF p.T.base (w.foldr (fun a H => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) H) F) g))
  by_cases hc : χ (Gf P.k P.r p.T.base.z p.T.base.z' g / ε) = 0
  · rw [Formalism.FourierDecayAlt.P.JCTx2.JF_cutF, hc]
    have hz : B.hsVec ((((0 : ℝ) : ℂ)) • B.JF p.T.base F g) = 0 := by
      unfold B.hsVec
      simp only [Complex.ofReal_zero, zero_smul, ContinuousLinearMap.zero_apply]
      rfl
    rw [hz]
    simp
  have hge : δ ≤ Gf P.k P.r p.T.base.z p.T.base.z' g / ε := by
    by_contra h
    exact hc (h0 _ (not_le.1 h))
  have hgt : δ₀ * ε < Gf P.k P.r p.T.base.z p.T.base.z' g := by
    have := (le_div_iff₀ hε).1 hge
    nlinarith
  set U := {x : B.Mat P.k P.r | δ₀ * ε < Gf P.k P.r p.T.base.z p.T.base.z' x} with hUdef
  have hU : IsOpen U :=
    isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf p.T.base.z p.T.base.z').continuous
  have he : ∀ x ∈ U ∩ B.GV P.k P.r, D.cutF p.T.base χ' F ε x = F x := by
    intro x hx
    unfold D.cutF
    have hx1 : δ₀ ≤ Gf P.k P.r p.T.base.z p.T.base.z' x / ε := (le_div_iff₀ hε).2 (le_of_lt hx.1)
    rw [h1 _ hx1]
    simp
  have hcut := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ' hF ε
  rw [jf_congr_level p.T.base hgG (fun x hx hGx =>
      fold_congr_open (M.sgn P p.l0) hU hcut hF he w x ⟨by show δ₀ * ε < _; rw [hGx]; exact hgt, hx⟩)]

end place

def NFPolFormAll : Prop :=
  P5.ThmPActual → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ χ' : ℝ → ℝ, C6.IsCut0 χ' → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
      ∀ ε : ℝ, 0 < ε →
        Integrable (topPD p (D.cutF p.T.base χ' (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε)
          (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w) ∧
        (pair0 p (D.cutF p.T.base χ' (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε)
          (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w).re =
          ∫ c, topPD p (D.cutF p.T.base χ' (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε)
            (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w c

def NFPairPtwAll : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ χ' : ℝ → ℝ, C6.IsCut0 χ' → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
      ∀ᵐ c : Fin (P.r + 1) → ℂ, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        topPD p (D.cutF p.T.base χ' (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε)
          (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w c =
        topD p (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) w c

def NFBetaLimAll : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
      Tendsto (fun ε : ℝ => (pair0 p (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀)
          (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w).re) (𝓝[>] 0)
        (𝓝 (pair0 p (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀)
          (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) w).re)

theorem nfHyp_mono {Cb c c' : ℝ} {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    {p : KB.Pl P Wp Wq} {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {A₀ : ℝ} {p₀ : ℕ} {χ χ' : ℝ → ℝ} {N : ℕ}
    (h : NFHyp Cb c p f A₀ p₀ χ N) (hc : c' ≤ c) (hχ' : C6.IsCut0 χ') : NFHyp Cb c' p f A₀ p₀ χ' N := by
  obtain ⟨-, a2, a3, a4, a5, a6⟩ := h
  refine ⟨hχ', a2, a3, a4, le_trans ?_ a5, a6⟩
  have hX : 0 ≤ ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) := by
    positivity
  have e : ∀ x : ℝ, x * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) =
      x * (((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3)) :=
    fun x => by ring
  rw [e, e]
  exact mul_le_mul_of_nonneg_right hc hX

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem nfTopIdAll_of (hA : P5.ThmPActual) (h3 : NFTopDomAll) (s1 : NFPolFormAll) (s2 : NFPairPtwAll)
    (s4 : NFBetaLimAll) : NFTopIdAll := by
  intro Cb
  obtain ⟨C1, H1⟩ := s1 hA Cb
  obtain ⟨C2, H2⟩ := s2 Cb
  obtain ⟨C3, H3⟩ := h3 Cb
  obtain ⟨C4, H4⟩ := s4 Cb
  refine ⟨max (max C1 C2) (max C3 C4), ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN
  have hχ : C6.IsCut0 χ := hH.1
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
  have hF := ckOn_fpm p p₀ hH.2.2.1 hid
  set F' := TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀ with hF'
  have m1 : C1 ≤ max (max C1 C2) (max C3 C4) := le_max_of_le_left (le_max_left _ _)
  have m2 : C2 ≤ max (max C1 C2) (max C3 C4) := le_max_of_le_left (le_max_right _ _)
  have m3 : C3 ≤ max (max C1 C2) (max C3 C4) := le_max_of_le_right (le_max_left _ _)
  have m4 : C4 ≤ max (max C1 C2) (max C3 C4) := le_max_of_le_right (le_max_right _ _)

  have hβ : Tendsto (fun ε : ℝ => (pair0 p (D.cutF p.T.base χκ F' ε) (D.cutF p.T.base χ F' ε) w).re) (𝓝[>] 0)
      (𝓝 (pair0 p F' F' w).re) := by
    refine (H4 Wp Wq P p f A₀ p₀ χ Y N (nfHyp_mono hH m4 hχ) w hw hN).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [pairing_truncation_locality p hF hχκ hκδ hχ0 hχκ1 w hε]

  obtain ⟨-, hA, hAi, hAb⟩ := H3 Wp Wq P p f A₀ p₀ χκ Y N (nfHyp_mono hH m3 hχκ) w hw hN
  obtain ⟨-, hB, hBi, hBb⟩ := H3 Wp Wq P p f A₀ p₀ χ Y N (nfHyp_mono hH m3 hχ) w hw hN
  have hT : Tendsto (fun ε : ℝ => ∫ c, topPD p (D.cutF p.T.base χκ F' ε) (D.cutF p.T.base χ F' ε) w c) (𝓝[>] 0)
      (𝓝 (∫ c, topD p F' w c)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun c => (hA c + hB c) / 2) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (H1 Wp Wq P p f A₀ p₀ χ Y N (nfHyp_mono hH m1 hχ) χκ hχκ w hw hN ε hε).1.aestronglyMeasurable
    · filter_upwards [hAb, hBb] with ε ha hb
      filter_upwards [ha, hb] with c hac hbc
      rw [Real.norm_eq_abs]
      refine (topPD_cs p _ _ w c).trans ?_
      have e1 := (le_abs_self (topD p (D.cutF p.T.base χκ F' ε) w c)).trans (le_of_eq (Real.norm_eq_abs _).symm)
      have e2 := (le_abs_self (topD p (D.cutF p.T.base χ F' ε) w c)).trans (le_of_eq (Real.norm_eq_abs _).symm)
      linarith
    · exact (hAi.add hBi).div_const 2
    · filter_upwards [H2 Wp Wq P p f A₀ p₀ χ Y N (nfHyp_mono hH m2 hχ) χκ hχκ w hw hN] with c hc
      exact tendsto_const_nhds.congr' (hc.mono fun ε h => h.symm)
  have hE : (fun ε : ℝ => (pair0 p (D.cutF p.T.base χκ F' ε) (D.cutF p.T.base χ F' ε) w).re) =ᶠ[𝓝[>] (0 : ℝ)]
      fun ε => ∫ c, topPD p (D.cutF p.T.base χκ F' ε) (D.cutF p.T.base χ F' ε) w c := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (H1 Wp Wq P p f A₀ p₀ χ Y N (nfHyp_mono hH m1 hχ) χκ hχκ w hw hN ε hε).2
  have huniq := tendsto_nhds_unique (hβ.congr' hE) hT
  show ∫ c, topD p F' w c = (p.RR F' 0 w [] []).re
  rw [← huniq, residual_pairing_eq_self_pairing p hF hw.1]

end

end Formalism.FourierDecayAlt.P.CutBP
