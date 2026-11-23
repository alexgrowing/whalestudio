import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsometryApplyEqOfFormSubNeZero

set_option autoImplicit false

open MeasureTheory Topology Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal

namespace GlobalTheory.PeterssonRigid

theorem conjT_isHermitian {r : ℕ} {M : Matrix (Fin r) (Fin r) ℂ} (hM : M.IsHermitian)
    (x : Matrix (Fin r) (Fin r) ℂ) : (xᵀ * M * x.map (starRingEnd ℂ)).IsHermitian := by
  have h := Matrix.isHermitian_mul_mul_conjTranspose xᵀ hM
  have e : (xᵀ)ᴴ = x.map (starRingEnd ℂ) := by ext a b; rfl
  rwa [e] at h

theorem det_conjT {r : ℕ} {M x : Matrix (Fin r) (Fin r) ℂ} (hM : M.det ≠ 0) (hx : x.det ≠ 0) :
    (xᵀ * M * x.map (starRingEnd ℂ)).det ≠ 0 := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    show x.map (starRingEnd ℂ) = (starRingEnd ℂ).mapMatrix x from rfl, ← RingHom.map_det]
  exact mul_ne_zero (mul_ne_zero hx hM) ((map_ne_zero _).2 hx)

theorem conjT_mul {r : ℕ} (M x y : Matrix (Fin r) (Fin r) ℂ) :
    (x * y)ᵀ * M * (x * y).map (starRingEnd ℂ) = yᵀ * (xᵀ * M * x.map (starRingEnd ℂ)) * y.map (starRingEnd ℂ) := by
  rw [Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

theorem conjT_one {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) :
    (1 : Matrix (Fin r) (Fin r) ℂ)ᵀ * M * (1 : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) = M := by
  simp

theorem conjT_cancel {r : ℕ} {x : Matrix (Fin r) (Fin r) ℂ} (hx : x.det ≠ 0) (M : Matrix (Fin r) (Fin r) ℂ) :
    (x⁻¹)ᵀ * (xᵀ * M * x.map (starRingEnd ℂ)) * (x⁻¹).map (starRingEnd ℂ) = M := by
  rw [← conjT_mul, Matrix.mul_nonsing_inv _ hx.isUnit, conjT_one]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem map_Gm_isHermitian {r : ℕ} (X : Data E r) (τ : E →+* ℂ) : (X.Gm.map τ).IsHermitian := by
  ext a b
  rw [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, ← X.Gm_herm b a]
  exact (IsCMField.complexEmbedding_complexConj E τ _).symm

theorem gram_isHermitian {r : ℕ} (X : Data E r) (τ : E →+* ℂ) (m : Matrix (Fin r) (Fin r) ℂ) :
    (gram τ X.Gm m).IsHermitian := by
  rw [FrameDegreeData.gram_eq]
  exact conjT_isHermitian (map_Gm_isHermitian X τ) m

theorem gram_zero_zero {n : ℕ} (X : Data E (n + 1)) {x : Frame X.Ψ (n + 1)} (hx : x ∈ X.dom) (τ : X.Ψ)
    (h1 : ∀ i, ‖dmin X.Gm x τ i‖ = 1) : gram τ.1 X.Gm (mat x τ) 0 0 = (psgn X.p0 1 : ℂ) := by
  let i : Fin (n + 1 + 1) := ⟨1, by omega⟩
  have e : dmin X.Gm x τ i = gram τ.1 X.Gm (mat x τ) 0 0 := by
    unfold dmin lminor
    exact Matrix.det_fin_one _
  have hp := (hx τ).2 i
  have hn := h1 i
  rw [e] at hp hn
  have hr : (((gram τ.1 X.Gm (mat x τ) 0 0).re : ℝ) : ℂ) = gram τ.1 X.Gm (mat x τ) 0 0 :=
    (gram_isHermitian X τ.1 _).coe_re_apply_self 0
  rw [← hr, Complex.norm_real, Real.norm_eq_abs] at hn
  rw [← hr]
  congr 1
  have ha := GlobalTheory.PeterssonCompare.abs_psgn X.p0 1
  change 0 < psgn X.p0 1 * _ at hp
  rcases (abs_eq zero_le_one).1 ha with h | h <;> rcases (abs_eq zero_le_one).1 hn with h' | h' <;>
    rw [h, h'] at hp <;> first | exact h'.trans h.symm | norm_num at hp

theorem rigid : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Comp : Type) (X : Comp → Data E r) (G : Type) [Group G] (Gi : Subgroup G) (dict : G → Σ k, Frame (X k).Ψ r) (ar : ∀ k, G → (X k).Ψ → Matrix (Fin r) (Fin r) ℂ) (J : ∀ k, (X k).Ψ → Matrix (Fin r) (Fin r) ℂ) (x0 : ∀ k, Frame (X k).Ψ r), (∀ k τ, (J k τ).IsHermitian ∧ (J k τ).det ≠ 0) → (∀ k (u : (X k).Ψ → Matrix (Fin r) (Fin r) ℂ), (∀ τ, (u τ)ᵀ * J k τ * (u τ).map (starRingEnd ℂ) = J k τ) → ∃ h ∈ Gi, ∀ τ, ar k h τ = u τ) → (∀ k, x0 k ∈ (X k).dom ∧ ∃ g, dict g = ⟨k, x0 k⟩) → (∀ g, ∀ h ∈ Gi, ∃ γ ∈ (X (dict g).1).Γ, dict (g * h) = ⟨(dict g).1, lact γ (rmul (dict g).2 fun τ => ((mat (x0 (dict g).1) τ)⁻¹ * ar (dict g).1 h τ * mat (x0 (dict g).1) τ : Matrix (Fin r) (Fin r) ℂ))⟩) → (∀ g, (dict g).2 ∈ (X (dict g).1).dom) → (∀ g τ i, ‖dmin (X (dict g).1).Gm (dict g).2 τ i‖ = 1) → (∀ k (τ : (X k).Ψ), ∃ t : ℝ, t ≠ 0 ∧ (X k).Gm.map τ.1 = (t : ℂ) • J k τ) ∧ ∀ g τ, gram τ.1 (X (dict g).1).Gm (mat (dict g).2 τ) = gram τ.1 (X (dict g).1).Gm (mat (x0 (dict g).1) τ) := by
  intro E _ _ _ r Comp X G _ Gi dict ar J x0 hJ hsurj hx0 hmul hdom hunit
  classical
  cases r with
  | zero => exact ⟨fun k τ => ⟨1, one_ne_zero, Subsingleton.elim _ _⟩, fun g τ => Subsingleton.elim _ _⟩
  | succ n =>
  have he : ∀ p : ℕ, (psgn p 1 : ℂ) ≠ 0 := by
    intro p h
    have ha := GlobalTheory.PeterssonCompare.abs_psgn p 1
    rw [Complex.ofReal_eq_zero.1 h] at ha
    norm_num at ha
  have h00 : ∀ g k x, dict g = ⟨k, x⟩ → ∀ τ : (X k).Ψ,
      gram τ.1 (X k).Gm (mat x τ) 0 0 = (psgn (X k).p0 1 : ℂ) := by
    intro g k x h τ
    have h1 := hdom g
    have h2 := hunit g
    rw [h] at h1 h2
    exact gram_zero_zero (X k) h1 τ (h2 τ)
  have key : ∀ g k x, dict g = ⟨k, x⟩ → ∀ τ : (X k).Ψ, ∃ t : ℝ, t ≠ 0 ∧
      gram τ.1 (X k).Gm (mat x τ) =
        (t : ℂ) • ((mat (x0 k) τ)ᵀ * J k τ * (mat (x0 k) τ).map (starRingEnd ℂ)) := by
    intro g k x h τ
    have hd : (mat (x0 k) τ).det ≠ 0 := ((hx0 k).1 τ).1
    refine GlobalTheory.hermitian_eq_smul_of_const_on_unitary_orbit _ _ _ 0 _ (he (X k).p0) (gram_isHermitian _ _ _) (conjT_isHermitian (hJ k τ).1 _)
      (det_conjT (hJ k τ).2 hd) fun u hu => ?_
    obtain ⟨a, ha, har⟩ := hsurj k (Function.update (fun _ => 1) τ (mat (x0 k) τ * u * (mat (x0 k) τ)⁻¹)) (by
      intro σ
      by_cases hσ : σ = τ
      · subst hσ
        rw [Function.update_self, conjT_mul, conjT_mul, hu, conjT_cancel hd]
      · rw [Function.update_of_ne hσ, conjT_one])
    have hm := hmul g a ha
    rw [h] at hm
    obtain ⟨γ, hγ, hm⟩ := hm
    have h1 := h00 _ _ _ hm τ
    rw [MajInv.gram_lact _ ((X k).Γ_stab γ hγ)] at h1
    have e : mat (rmul x fun τ => ((mat (x0 k) τ)⁻¹ * ar k a τ * mat (x0 k) τ :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) τ = mat x τ * u := by
      show mat x τ * ((mat (x0 k) τ)⁻¹ * ar k a τ * mat (x0 k) τ) = _
      rw [har, Function.update_self, Matrix.mul_assoc (mat (x0 k) τ), Matrix.nonsing_inv_mul_cancel_left _ _ hd.isUnit,
        Matrix.nonsing_inv_mul_cancel_right _ _ hd.isUnit]
    dsimp only at h1
    rw [e, FrameDegreeData.gram_mul] at h1
    exact h1
  refine ⟨fun k τ => ?_, fun g τ => ?_⟩
  · obtain ⟨g, hg⟩ := (hx0 k).2
    obtain ⟨t, ht, h⟩ := key g k _ hg τ
    refine ⟨t, ht, ?_⟩
    have hd : (mat (x0 k) τ).det ≠ 0 := ((hx0 k).1 τ).1
    rw [← conjT_cancel hd ((X k).Gm.map τ.1), ← FrameDegreeData.gram_eq, h, Matrix.mul_smul, Matrix.smul_mul, conjT_cancel hd]
  · obtain ⟨g', hg'⟩ := (hx0 (dict g).1).2
    obtain ⟨t, -, h⟩ := key g _ _ rfl τ
    obtain ⟨t', -, h'⟩ := key g' _ _ hg' τ
    have a := h00 g _ _ rfl τ
    have a' := h00 g' _ _ hg' τ
    rw [h, Matrix.smul_apply, smul_eq_mul] at a
    rw [h', Matrix.smul_apply, smul_eq_mul] at a'
    have hb : ((mat (x0 (dict g).1) τ)ᵀ * J _ τ * (mat (x0 (dict g).1) τ).map (starRingEnd ℂ)) 0 0 ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at a
      exact he _ a.symm
    rw [h, h', mul_right_cancel₀ hb (a.trans a'.symm)]

end GlobalTheory.PeterssonRigid
