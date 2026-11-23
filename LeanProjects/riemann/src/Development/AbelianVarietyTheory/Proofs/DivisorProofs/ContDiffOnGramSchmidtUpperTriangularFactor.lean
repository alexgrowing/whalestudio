import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDomOfOrth
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.SUChartSection.GSSmooth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

section Mat

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {s : Set W}

theorem cdo_det {m : Type} [Fintype m] [DecidableEq m] (f : W → Matrix m m ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun w => f w i j) s) : ContDiffOn ℝ ∞ (fun w => (f w).det) s := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => hf _ _)

theorem cdo_inv {m : Type} [Fintype m] [DecidableEq m] (f : W → Matrix m m ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun w => f w i j) s) (hd : ∀ w ∈ s, (f w).det ≠ 0) (i j : m) :
    ContDiffOn ℝ ∞ (fun w => (f w)⁻¹ i j) s := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', Matrix.adjugate_apply]
  refine ((cdo_det f hf).inv hd).mul (cdo_det _ fun a b => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffOn_const
  · exact hf _ _

theorem cdo_mul {m : Type} [Fintype m] (f g : W → Matrix m m ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun w => f w i j) s) (hg : ∀ i j, ContDiffOn ℝ ∞ (fun w => g w i j) s) (i j : m) :
    ContDiffOn ℝ ∞ (fun w => (f w * g w) i j) s := by
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun k _ => (hf _ _).mul (hg _ _)

end Mat

theorem contDiff_nmat (X : Data E r) (τ : X.Ψ) (a b : Fin r) :
    ContDiff ℝ ∞ fun w : V (nd X) => mat (nmat X w) τ a b := by
  show ContDiff ℝ ∞ fun w : V (nd X) => nmat X w τ a b
  unfold nmat
  split_ifs
  · exact ((EuclideanSpace.proj _ : V (nd X) →L[ℂ] ℂ).restrictScalars ℝ).contDiff
  · exact contDiff_const
  · exact contDiff_const

theorem contDiff_Gw (X : Data E r) (τ : X.Ψ) (a b : Fin r) :
    ContDiff ℝ ∞ fun w : V (nd X) => PoinPf.Gw X w τ a b := by
  simp only [PoinPf.Gw, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  refine ContDiff.sum fun k _ => ContDiff.mul
    (ContDiff.sum fun l _ => (contDiff_nmat X τ l a).mul contDiff_const) ?_
  exact Complex.conjCLE.contDiff.comp (contDiff_nmat X τ k b)

theorem blk_det_on (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) (c : Fin r) :
    ∀ w ∈ {w : V (nd X) | cpt X x w ∈ X.dom}, (FrameDegreeData.blk (PoinPf.Gw X w τ) c).det ≠ 0 := by
  intro w hw
  have h := FrameDegreeData.blk_det X hw τ c
  rwa [gram_cpt X hx] at h

theorem cdo_gsU (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) (j c : Fin r) :
    ContDiffOn ℝ ∞ (fun w => gsU X w τ j c) {w : V (nd X) | cpt X x w ∈ X.dom} := by
  simp only [gsU, FrameDegreeData.uMat, Matrix.of_apply]
  split_ifs with h1 h2
  · exact contDiffOn_const
  · refine ContDiffOn.neg ?_
    simp only [Matrix.vecMul, dotProduct]
    refine ContDiffOn.sum fun m _ => ContDiffOn.mul ?_ ?_
    · exact (contDiff_Gw X τ c (Fin.castLE c.isLt.le m)).contDiffOn
    · exact cdo_inv (fun w => FrameDegreeData.blk (PoinPf.Gw X w τ) c)
        (fun a b => (contDiff_Gw X τ (Fin.castLE c.isLt.le a) (Fin.castLE c.isLt.le b)).contDiffOn)
        (blk_det_on X hx τ c) _ _
  · exact contDiffOn_const

theorem cdo_q (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) (i j : Fin r) :
    ContDiffOn ℝ ∞ (fun w => ((gsU X w τ)ᵀ * PoinPf.Gw X w τ * (gsU X w τ).map (starRingEnd ℂ)) i j)
      {w : V (nd X) | cpt X x w ∈ X.dom} := by
  refine cdo_mul _ _ (fun a b => cdo_mul _ _ (fun a' b' => ?_) (fun a' b' => (contDiff_Gw X τ a' b').contDiffOn) a b)
    (fun a b => ?_) i j
  · exact cdo_gsU X hx τ b' a'
  · exact Complex.conjCLE.contDiff.comp_contDiffOn (cdo_gsU X hx τ a b)

theorem q_eq_dOf (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (w : V (nd X)) (τ : X.Ψ) (k : Fin r) :
    ((gsU X w τ)ᵀ * PoinPf.Gw X w τ * (gsU X w τ).map (starRingEnd ℂ)) k k = FrameDegreeData.dOf X (cpt X x w) τ k := by
  simp only [FrameDegreeData.dOf, FrameDegreeData.uOf, FrameDegreeData.gram_mul, gram_cpt X hx, gsU]

theorem cdo_gsS (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) (k : Fin r) :
    ContDiffOn ℝ ∞ (fun w => gsS X w τ k) {w : V (nd X) | cpt X x w ∈ X.dom} := by
  set S := {w : V (nd X) | cpt X x w ∈ X.dom}
  have hpos : ∀ w ∈ S, 0 < sgn X.p0 k *
      (((gsU X w τ)ᵀ * PoinPf.Gw X w τ * (gsU X w τ).map (starRingEnd ℂ)) k k).re := by
    intro w hw
    rw [q_eq_dOf X hx w τ k]
    exact FrameDegreeData.sgn_dOf_pos X hw τ k
  have hf : ContDiffOn ℝ ∞ (fun w => sgn X.p0 k *
      (((gsU X w τ)ᵀ * PoinPf.Gw X w τ * (gsU X w τ).map (starRingEnd ℂ)) k k).re) S :=
    contDiffOn_const.mul (Complex.reCLM.contDiff.comp_contDiffOn (cdo_q X hx τ k k))
  refine ContDiffOn.congr (ContDiffOn.inv (hf.sqrt fun w hw => (hpos w hw).ne')
    fun w hw => (Real.sqrt_pos.2 (hpos w hw)).ne') fun w hw => ?_
  have h := hpos w hw
  simp only [gsS]
  congr 2
  rcases FrameDegreeData.sgn_sq X.p0 k with hs | hs <;> rw [hs] at h ⊢
  · rw [one_mul] at h ⊢
    exact abs_of_pos h
  · rw [neg_one_mul] at h ⊢
    exact abs_of_neg (neg_pos.1 h)

theorem gsB_contDiffOn : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r},
    IsOrth X x → ∀ (τ : X.Ψ) (a b : Fin r),
      ContDiffOn ℝ ∞ (fun w => gsB X w τ a b) {w | cpt X x w ∈ X.dom} := by
  intro E _ _ _ r X x hx τ a b
  have e : (fun w => gsB X w τ a b) = fun w => gsU X w τ a b * ((gsS X w τ b : ℝ) : ℂ) := by
    funext w
    simp only [gsB, Matrix.mul_diagonal]
  rw [e]
  exact (cdo_gsU X hx τ a b).mul (Complex.ofRealCLM.contDiff.comp_contDiffOn (cdo_gsS X hx τ b))

end GlobalTheory.SUChartSection.GSSmooth
