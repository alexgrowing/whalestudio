import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxC
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.RightMulBorelFirstColumn

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ComplexConjugate Matrix

namespace GlobalTheory.TwoLines

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

noncomputable def leviCol (X : Data E 2) (x0 : Frame X.Ψ 2) (τ : X.Ψ) (z : V (nd X))
    (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun w => ((Real.log (colSq (cpt X x0 w) τ) : ℝ) : ℂ)) z ξ).re

theorem wd_affine {n : ℕ} (c d : ℂ) (k j : Fin n) (z : V n) :
    wd n j (fun w : V n => c + d * w k) z = if j = k then d else 0 := by
  have h : HasFDerivAt (fun w : V n => c + d * w k)
      (d • (EuclideanSpace.proj k : V n →L[ℂ] ℂ)) z :=
    ((EuclideanSpace.proj k : V n →L[ℂ] ℂ).hasFDerivAt.const_mul d).const_add c
  rw [wd_of_differentiableAt h.differentiableAt, h.fderiv]
  simp [bas, eq_comm]

theorem leviCol_eq (X : Data E 2) {x0 : Frame X.Ψ 2} {τ : X.Ψ} (h : (mat x0 τ).det ≠ 0)
    (z : V (nd X)) (ξ : Fin (nd X) → ℂ) :
    0 ≤ leviCol X x0 τ z ξ ∧ (ξ (idx X τ) ≠ 0 → 0 < leviCol X x0 τ z ξ) := by
  let g : Fin 2 → V (nd X) → ℂ := fun a w => x0 τ a 0 + x0 τ a 1 * w (idx X τ)
  have hs : ∀ w, colSq (cpt X x0 w) τ = sqNorm fun a => g a w := fun w => by
    simp [colSq, sqNorm, compact_frame_first_column, g, Complex.normSq_eq_norm_sq]
  have hpos : 0 < sqNorm fun a => g a z := hs z ▸ colSq_pos (by rwa [det_cpt])
  have hne : (fun a => g a z) ≠ 0 := fun h0 => by rw [h0] at hpos; simp [sqNorm] at hpos
  have hcd : ∀ a, ContDiffAt ℂ 2 (g a) z := fun a =>
    (contDiff_const.add (contDiff_const.mul
      (EuclideanSpace.proj (idx X τ) : V (nd X) →L[ℂ] ℂ).contDiff)).contDiffAt
  have hL := leviLogNormSq (nd X) 2 g z ξ hcd hne
  have hJ : wJac (nd X) 2 g z *ᵥ ξ = fun a => x0 τ a 1 * ξ (idx X τ) := by
    funext a
    simp [wJac, Matrix.mulVec, dotProduct, g, wd_affine]
  unfold leviCol
  simp only [hs]
  rw [hL, Complex.ofReal_re, hJ]
  refine ⟨div_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) hpos.le, fun hξ =>
    div_pos (sqNorm_pos fun h0 => ?_) hpos⟩
  rw [projPerp_mulVec] at h0
  set c := ((sqNorm fun a => g a z : ℝ) : ℂ)⁻¹ * (star (fun a => g a z) ⬝ᵥ fun a => x0 τ a 1 * ξ (idx X τ))
  have e0 : x0 τ 0 1 * ξ (idx X τ) - c * (x0 τ 0 0 + x0 τ 0 1 * z (idx X τ)) = 0 := congrFun h0 0
  have e1 : x0 τ 1 1 * ξ (idx X τ) - c * (x0 τ 1 0 + x0 τ 1 1 * z (idx X τ)) = 0 := congrFun h0 1
  rw [det_mat] at h
  have hc : c = 0 := by
    apply (mul_eq_zero_iff_right h).1
    linear_combination x0 τ 0 1 * e1 - x0 τ 1 1 * e0
  apply mul_ne_zero h hξ
  rw [hc] at e0 e1
  linear_combination x0 τ 0 0 * e1 - x0 τ 1 0 * e0

theorem logCol_cd (X : Data E 2) {x0 : Frame X.Ψ 2} {τ : X.Ψ} (h : (mat x0 τ).det ≠ 0)
    (z : V (nd X)) : ContDiffAt ℝ 2 (fun w => Real.log (colSq (cpt X x0 w) τ)) z := by
  refine ContDiffAt.log ?_ (colSq_pos (by rwa [det_cpt])).ne'
  have hc : ∀ a, ContDiffAt ℝ 2 (fun w => ‖cpt X x0 w τ a 0‖ ^ 2) z := fun a =>
    (((IW.cpt_entry_cd X x0 τ a 0).restrict_scalars ℝ).of_le HE.two_le_inf).contDiffAt.norm_sq ℂ
  exact (hc 0).add (hc 1)

omit [NumberField E] [IsCMField E] in
theorem univ_two {Ψ : Finset (E →+* ℂ)} {τ₁ τ₂ : Ψ} (hall : ∀ τ, τ = τ₁ ∨ τ = τ₂) [DecidableEq Ψ] :
    (Finset.univ : Finset Ψ) = {τ₁, τ₂} := by
  ext τ; simpa using hall τ

omit [NumberField E] [IsCMField E] in
theorem prod_two {Ψ : Finset (E →+* ℂ)} {τ₁ τ₂ : Ψ} (hne : τ₁ ≠ τ₂) (hall : ∀ τ, τ = τ₁ ∨ τ = τ₂)
    {M : Type*} [CommMonoid M] (f : Ψ → M) : ∏ τ, f τ = f τ₁ * f τ₂ := by
  classical
  rw [univ_two hall, Finset.prod_pair hne]

omit [NumberField E] [IsCMField E] in
theorem sum_two {Ψ : Finset (E →+* ℂ)} {τ₁ τ₂ : Ψ} (hne : τ₁ ≠ τ₂) (hall : ∀ τ, τ = τ₁ ∨ τ = τ₂)
    {M : Type*} [AddCommMonoid M] (f : Ψ → M) : ∑ τ, f τ = f τ₁ + f τ₂ := by
  classical
  rw [univ_two hall, Finset.sum_pair hne]

theorem leviM_phla {X : Data E 2} (hG : X.Gm = 1) (hp : X.p0 = 2) {τ₁ τ₂ : X.Ψ} (hne : τ₁ ≠ τ₂)
    (hall : ∀ τ, τ = τ₁ ∨ τ = τ₂) {x0 : Frame X.Ψ 2} (hx : x0 ∈ X.dom) (la : Wt X.Ψ 2)
    (z : V (nd X)) (ξ : Fin (nd X) → ℂ) :
    leviM X (phla X la) x0 z ξ = (la τ₁ 0 - la τ₁ 1 : ℝ) * leviCol X x0 τ₁ z ξ +
      (la τ₂ 0 - la τ₂ 1 : ℝ) * leviCol X x0 τ₂ z ξ := by
  have h1 := logCol_cd X (hx τ₁).1 z
  have h2 := logCol_cd X (hx τ₂).1 z
  unfold leviM leviCol
  simp only [phla_cpt hG hp hx, sum_two hne hall]
  rw [Y.LocalMaximumSecondDerivative.leviV_ofReal_add ((contDiffAt_const.mul h1).add contDiffAt_const)
    ((contDiffAt_const.mul h2).add contDiffAt_const), Y.leviV_const_mul h1, Y.leviV_const_mul h2,
    Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]

theorem leviCol_add_pos {X : Data E 2} {τ₁ τ₂ : X.Ψ}
    (hall : ∀ τ, τ = τ₁ ∨ τ = τ₂) {x0 : Frame X.Ψ 2} (hx : x0 ∈ X.dom)
    (z : V (nd X)) {ξ : Fin (nd X) → ℂ} (hξ : ξ ≠ 0) :
    0 < leviCol X x0 τ₁ z ξ + leviCol X x0 τ₂ z ξ := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hξ
  obtain ⟨τ, rfl⟩ := idx_surjective X k
  have h1 := leviCol_eq X (hx τ₁).1 z ξ
  have h2 := leviCol_eq X (hx τ₂).1 z ξ
  rcases hall τ with rfl | rfl
  · linarith [h1.2 hk, h2.1]
  · linarith [h2.2 hk, h1.1]

def idF (Ψ : Finset (E →+* ℂ)) : Frame Ψ 2 := fun _ => ![![1, 0], ![0, 1]]

def swF (Ψ : Finset (E →+* ℂ)) : Frame Ψ 2 := fun _ => ![![0, 1], ![1, 0]]

theorem isOrth_idF {X : Data E 2} (hG : X.Gm = 1) (hp : X.p0 = 2) : IsOrth X (idF X.Ψ) := by
  intro τ
  ext a b
  rw [hG, hp, gram_one]
  fin_cases a <;> fin_cases b <;> simp [idF, sgn]

theorem first_minimum_bounded_below {X : Data E 2} (hG : X.Gm = 1) (hp : X.p0 = 2) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ X.dom, ε ≤ X.la1 x := by
  obtain ⟨h1, h2, h3⟩ := ClosedDiscontinuity.firstMinimum_invariant_continuous_pos_on_frames 2 X two_pos
  have hsub : {x : Frame X.Ψ 2 | IsOrth X x} ⊆ X.dom := fun x hx => IW.orth_mem_dom X x hx
  obtain ⟨y, hy, hmin⟩ := (isCompact_orth hG hp).exists_isMinOn ⟨_, isOrth_idF hG hp⟩ (h2.mono hsub)
  refine ⟨_, h3 y (hsub hy), fun x hx => ?_⟩
  obtain ⟨x1, ho, b, hb, rfl⟩ := ortho_holds 2 X x hx
  have := h1 1 X.Γ.one_mem x1 (hsub ho) b hb
  rw [lact_one'] at this
  rw [this]
  exact hmin ho

end GlobalTheory.TwoLines
