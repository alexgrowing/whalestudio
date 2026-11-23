import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Fischer
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MeasurePreservingMulLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralTransportHermitianFrameChartMeasure

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker.Ortho

open ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData GlobalTheory.SW.Slab

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

noncomputable def tri (x : Frame X.Ψ r) : Frame X.Ψ r :=
  fun τ => ((mat (bOf X x) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)

end GlobalTheory.Ker.Ortho

namespace GlobalTheory.Ker

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
private lemma continuous_bOf :
    Continuous fun p : X.dom => _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X p.1 := by
  have hG : ∀ τ : X.Ψ, Continuous fun p : X.dom => _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat p.1 τ) := fun τ =>
    continuous_pi fun a => continuous_pi fun b =>
      (_root_.GlobalTheory.SW.Slab.continuous_gram X τ a b).comp continuous_subtype_val
  have hU : ∀ τ : X.Ψ, Continuous fun p : X.dom => _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.uOf X p.1 τ := by
    intro τ
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.uOf _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.uMat
    refine continuous_pi fun j => continuous_pi fun c => ?_
    simp only [Matrix.of_apply]
    split_ifs with h1 h2
    · exact continuous_const
    · have hinv : Continuous fun p : X.dom =>
          (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.blk (_root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat p.1 τ)) c)⁻¹ := by
        refine continuous_iff_continuousAt.2 fun p => ?_
        refine (continuousAt_matrix_inv _ ?_).comp ?_
        · rw [Ring.inverse_eq_inv']
          exact continuousAt_inv₀ (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.blk_det X p.2 τ c)
        · unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.blk
          exact ((hG τ).matrix_submatrix _ _).continuousAt
      have hrow : Continuous fun p : X.dom => _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.rowc (_root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat p.1 τ)) c := by
        unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.rowc
        exact continuous_pi fun m => (continuous_apply_apply _ _).comp (hG τ)
      exact ((continuous_apply _).comp (hrow.matrix_vecMul hinv)).neg
    · exact continuous_const
  have hM : ∀ τ : X.Ψ, Continuous fun p : X.dom => _root_.ReciprocityTheory.ChartRestriction.G.FD.mat p.1 τ := fun τ =>
    (continuous_apply τ).comp continuous_subtype_val
  refine continuous_pi fun τ => ?_
  have hMU := (hM τ).matrix_mul (hU τ)
  have hent : ∀ a b, Continuous fun p : X.dom => (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat p.1 τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.uOf X p.1 τ) a b :=
    fun a b => (continuous_apply_apply a b).comp hMU
  have hd : ∀ k, Continuous fun p : X.dom => _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.dOf X p.1 τ k := by
    intro k
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.dOf _root_.ReciprocityTheory.ChartRestriction.G.FD.gram _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC _root_.ReciprocityTheory.ChartRestriction.G.FD.col
    simp only [Matrix.of_apply]
    exact continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ =>
      ((hent a k).mul continuous_const).mul (Complex.continuous_conj.comp (hent b k))
  have hs : Continuous fun p : X.dom => _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.sOf X p.1 τ := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.sOf
    refine continuous_pi fun k => Complex.continuous_ofReal.comp ?_
    exact Continuous.inv₀ (Real.continuous_sqrt.comp (continuous_abs.comp
      (Complex.continuous_re.comp (hd k)))) fun p => (Real.sqrt_pos.2 (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.abs_re_pos X p.2 τ k)).ne'
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf
  exact (hU τ).matrix_mul hs.matrix_diagonal

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in

theorem _root_.GlobalTheory.Ker.exists_orthonormalisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), ∃ o b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, ContinuousOn o X.dom ∧ ContinuousOn b X.dom ∧ (∀ x ∈ X.dom, _root_.GlobalTheory.Ker.IsONFr X (o x) ∧ b x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r ∧ x = _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (o x) (b x) ∧ (∀ (τ : X.Ψ) (i : Fin r), ‖b x τ i i‖ ^ 2 = ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ / _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖) ∧ ∀ u : X.Ψ → Matrix (Fin r) (Fin r) ℂ, (∀ (τ : X.Ψ) v w, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (u τ *ᵥ v) (u τ *ᵥ w) = _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm v w) → X.lmulC u x ∈ X.dom ∧ o (X.lmulC u x) = X.lmulC u (o x)) ∧ ∃ δ : ℝ, 0 < δ ∧ _root_.GlobalTheory.SW.slab X δ ⊆ X.dom ∧ ∃ C : ℝ, ∀ x ∈ _root_.GlobalTheory.SW.slab X δ, ∀ τ i j, ‖b x τ i j‖ ≤ C ∧ C⁻¹ ≤ ‖b x τ i i‖ := by
  intro E _ _ _ r X
  have hcontB := continuous_bOf X
  have hBor : ∀ x ∈ X.dom, _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r := fun x hx => _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem X hx
  have hdetB : ∀ x ∈ X.dom, ∀ τ, IsUnit (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ).det := fun x hx τ =>
    isUnit_iff_ne_zero.2 (hBor x hx τ).1
  obtain ⟨δ₀, hδ₀, hslab⟩ := _root_.GlobalTheory.SW.thin_slab E r X
  have hslab0 := hslab δ₀ hδ₀ le_rfl
  have hfac : ∀ x ∈ X.dom,
      x = _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x)) (_root_.GlobalTheory.Ker.Ortho.tri X x) := by
    intro x hx
    funext τ
    show x τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ)⁻¹
    rw [Matrix.mul_nonsing_inv_cancel_right _ _ (hdetB x hx τ)]
    rfl
  have hON : ∀ x ∈ X.dom, _root_.GlobalTheory.Ker.IsONFr X (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x)) :=
    fun x hx => _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf X hx
  have hOdom : ∀ x ∈ X.dom, _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) ∈ X.dom := fun x hx =>
    hslab0.2.1 (hslab0.2.2.1 _ (hON x hx))
  have hTri : ∀ x ∈ X.dom, _root_.GlobalTheory.Ker.Ortho.tri X x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r := by
    intro x hx
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor
    simp only [Set.mem_setOf_eq]
    intro τ
    have hu := hdetB x hx τ
    haveI := Matrix.invertibleOfIsUnitDet _ hu
    refine ⟨left_ne_zero_of_mul_eq_one (Matrix.det_nonsing_inv_mul_det _ hu), fun a c hca => ?_⟩
    exact Matrix.blockTriangular_inv_of_blockTriangular (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.upper_of_bor X (hBor x hx) τ) hca
  have hsgn : ∀ i : Fin (r + 1), ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.lminor (_root_.GlobalTheory.SW.sgnM X) i‖ = 1 := by
    intro i
    rw [_root_.GlobalTheory.SW.Slab.lminor_sgnM]
    rcases _root_.GlobalTheory.SW.Slab.psgn_sq X.p0 i with h | h <;> simp [h]
  have hdminON : ∀ x ∈ X.dom, ∀ τ i,
      ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x)) τ i‖ = 1 := by
    intro x hx τ i
    show ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.lminor (_root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x)) τ)) i‖ = 1
    rw [hON x hx τ, hsgn]
  have hdiag : ∀ x ∈ X.dom, ∀ (τ : X.Ψ) (i : Fin r), ‖_root_.GlobalTheory.Ker.Ortho.tri X x τ i i‖ ^ 2 =
      ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ / _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ := by
    intro x hx τ i
    have h := _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ratio_rmul X _ (hOdom x hx) (hTri x hx) τ i
    rw [← hfac x hx] at h
    rw [h, norm_div, hdminON x hx, hdminON x hx, div_one, mul_one]
  have hequiv : ∀ x ∈ X.dom, ∀ u : X.Ψ → Matrix (Fin r) (Fin r) ℂ,
      (∀ (τ : X.Ψ) v w, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (u τ *ᵥ v) (u τ *ᵥ w) = _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm v w) →
      X.lmulC u x ∈ X.dom ∧ _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (X.lmulC u x) (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X (X.lmulC u x)) =
        X.lmulC u (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x)) := by
    intro x hx u hu
    have hg : ∀ τ : X.Ψ, _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (X.lmulC u x) τ) =
        _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) := fun τ =>
      _root_.GlobalTheory.SW.Slab.gram_lmulC X hu τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)
    have hdm : ∀ τ i, _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (X.lmulC u x) τ i = _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i := fun τ i => by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin
      rw [hg τ]
    refine ⟨?_, ?_⟩
    · have hx' := hx
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom _root_.ReciprocityTheory.ChartRestriction.G.FD.GG at hx' ⊢
      simp only [Set.mem_setOf_eq] at hx' ⊢
      intro τ
      obtain ⟨-, hpos⟩ := hx' τ
      refine ⟨fun h0 => ?_, fun i => by rw [hdm τ i]; exact hpos i⟩
      have hl := hpos (Fin.last r)
      have hlast : _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ (Fin.last r) = (_root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)).det := by
        unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin _root_.ReciprocityTheory.ChartRestriction.G.FD.lminor
        rfl
      have hdg := _root_.GlobalTheory.SW.Slab.det_gram X τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (X.lmulC u x) τ)
      rw [hg τ, h0] at hdg
      simp only [zero_mul, map_zero] at hdg
      rw [hlast, hdg] at hl
      simp at hl
    · have hB : _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X (X.lmulC u x) = _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x := by
        funext τ
        show _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.uOf X (X.lmulC u x) τ * diagonal (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.sOf X (X.lmulC u x) τ) =
          _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.uOf X x τ * diagonal (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.sOf X x τ)
        have hO : _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.uOf X (X.lmulC u x) τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.uOf X x τ := by
          unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.uOf
          rw [hg τ]
        have hS : _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.sOf X (X.lmulC u x) τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.sOf X x τ := by
          unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.sOf _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.dOf
          rw [hO]
          have h2 : _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (X.lmulC u x) τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.uOf X x τ) =
              _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.uOf X x τ) := by
            rw [show _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (X.lmulC u x) τ = u τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ from rfl, Matrix.mul_assoc]
            exact _root_.GlobalTheory.SW.Slab.gram_lmulC X hu τ _
          rw [h2]
        rw [hO, hS]
      rw [hB]
      funext τ
      show _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (X.lmulC u x) τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ =
        u τ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ)
      rw [show _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (X.lmulC u x) τ = u τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ from rfl, Matrix.mul_assoc]
  have hM : ∀ τ : X.Ψ, Continuous fun p : X.dom => _root_.ReciprocityTheory.ChartRestriction.G.FD.mat p.1 τ := fun τ =>
    (continuous_apply τ).comp continuous_subtype_val
  have hBτ : ∀ τ : X.Ψ, Continuous fun p : X.dom => _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X p.1) τ := fun τ =>
    (continuous_apply τ).comp hcontB
  refine ⟨fun x => _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x), _root_.GlobalTheory.Ker.Ortho.tri X, ?_, ?_,
    fun x hx => ⟨hON x hx, hTri x hx, hfac x hx, hdiag x hx, fun u hu => hequiv x hx u hu⟩, ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    refine continuous_pi fun τ => ?_
    exact (hM τ).matrix_mul (hBτ τ)
  · rw [continuousOn_iff_continuous_restrict]
    refine continuous_pi fun τ => ?_
    show Continuous fun p : X.dom => (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X p.1) τ)⁻¹
    refine continuous_iff_continuousAt.2 fun p => ?_
    refine (continuousAt_matrix_inv _ ?_).comp (hBτ τ).continuousAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (hdetB p.1 p.2 τ).ne_zero
  · obtain ⟨δ₁, hδ₁, hδ₁le, hnear⟩ := _root_.GlobalTheory.SW.Slab.exists_lminor_near (_root_.GlobalTheory.SW.sgnM X)
    obtain ⟨C₀, -, hC⟩ := _root_.GlobalTheory.SW.Slab.exists_bound_upper (fun a : Fin r => (_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℂ))
      (fun a => _root_.GlobalTheory.SW.Slab.norm_sgn X.p0 a) r
    have hδ : 0 < min δ₀ δ₁ := lt_min hδ₀ hδ₁
    have hsub := (hslab _ hδ (min_le_left _ _)).2.1
    refine ⟨min δ₀ δ₁, hδ, hsub, max C₀ 2, ?_⟩
    intro x hxs τ i j
    have hx : x ∈ X.dom := hsub hxs
    have hxs' : ∀ (τ : X.Ψ) (a b : Fin r), ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) a b -
        _root_.GlobalTheory.SW.sgnM X a b‖ < min δ₀ δ₁ := hxs
    have hdmin : ∀ k : Fin (r + 1), 1 / 2 < ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ k‖ ∧ ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ k‖ < 3 / 2 := by
      intro k
      have hclose : ∀ a b : Fin r, ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) a b -
          _root_.GlobalTheory.SW.sgnM X a b‖ < δ₁ := fun a b =>
        (hxs' τ a b).trans_le (min_le_right _ _)
      have h : ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.lminor (_root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)) k -
          _root_.ReciprocityTheory.ChartRestriction.G.FD.lminor (_root_.GlobalTheory.SW.sgnM X) k‖ < 1 / 2 := hnear _ hclose k
      have hk : ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.lminor (_root_.GlobalTheory.SW.sgnM X) k‖ = 1 := hsgn k
      have hd : _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ k = _root_.ReciprocityTheory.ChartRestriction.G.FD.lminor (_root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)) k := rfl
      have h1 := norm_sub_norm_le (_root_.ReciprocityTheory.ChartRestriction.G.FD.lminor (_root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)) k)
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.lminor (_root_.GlobalTheory.SW.sgnM X) k)
      have h2 := norm_sub_norm_le (_root_.ReciprocityTheory.ChartRestriction.G.FD.lminor (_root_.GlobalTheory.SW.sgnM X) k)
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.lminor (_root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)) k)
      rw [norm_sub_rev] at h2
      rw [hd]
      constructor <;> linarith
    have hTa : ∀ a : Fin r, 1 / 2 ≤ ‖_root_.GlobalTheory.Ker.Ortho.tri X x τ a a‖ := by
      intro a
      have hsq := hdiag x hx τ a
      rw [norm_div] at hsq
      obtain ⟨h1, h2⟩ := hdmin a.succ
      obtain ⟨h3, h4⟩ := hdmin a.castSucc
      have hq : 1 / 4 ≤ ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ a.succ‖ / ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ a.castSucc‖ := by
        rw [le_div_iff₀ (by linarith)]
        linarith
      nlinarith [norm_nonneg (_root_.GlobalTheory.Ker.Ortho.tri X x τ a a)]
    have hGram : ∀ a c : Fin r,
        ‖((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.GlobalTheory.Ker.Ortho.tri X x) τ).transpose *
          diagonal (fun a : Fin r => (_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℂ)) *
          (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.GlobalTheory.Ker.Ortho.tri X x) τ).map (starRingEnd ℂ)) a c‖ ≤ 2 := by
      intro a c
      have hx2 : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x)) τ *
          _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.GlobalTheory.Ker.Ortho.tri X x) τ := congrFun (hfac x hx) τ
      have hG : (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.GlobalTheory.Ker.Ortho.tri X x) τ).transpose *
          diagonal (fun a : Fin r => (_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℂ)) *
          (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.GlobalTheory.Ker.Ortho.tri X x) τ).map (starRingEnd ℂ) =
          _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) := by
        rw [hx2, _root_.GlobalTheory.FlagTransport.gram_mul_right, hON x hx τ]
        rfl
      have hSd : ‖_root_.GlobalTheory.SW.sgnM X a c‖ ≤ 1 := by
        unfold _root_.GlobalTheory.SW.sgnM
        by_cases hac : a = c
        · subst hac
          rw [diagonal_apply_eq]
          exact (_root_.GlobalTheory.SW.Slab.norm_sgn _ _).le
        · simp [diagonal, hac]
      have hclose := hxs' τ a c
      have hle : min δ₀ δ₁ ≤ 1 := (min_le_right _ _).trans hδ₁le
      rw [hG]
      calc ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) a c‖
          ≤ ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) a c - _root_.GlobalTheory.SW.sgnM X a c‖ +
            ‖_root_.GlobalTheory.SW.sgnM X a c‖ := norm_le_norm_sub_add _ _
        _ ≤ 2 := by linarith
    have hbd := hC (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.GlobalTheory.Ker.Ortho.tri X x) τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.upper_of_bor X (hTri x hx) τ)
      (fun a h0 => by
        have := hTa a
        rw [show _root_.GlobalTheory.Ker.Ortho.tri X x τ a a = 0 from h0, norm_zero] at this
        linarith)
      (fun a => by
        rw [norm_inv]
        exact inv_le_of_inv_le₀ (by norm_num)
          ((by norm_num : (2 : ℝ)⁻¹ = 1 / 2).le.trans (hTa a)))
      hGram i i.isLt j
    refine ⟨hbd.trans (le_max_left _ _), ?_⟩
    calc (max C₀ 2)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) (le_max_right _ _)
      _ ≤ ‖_root_.GlobalTheory.Ker.Ortho.tri X x τ i i‖ := by have := hTa i; norm_num at this ⊢; linarith

end GlobalTheory.Ker
