import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.PluriharmonicHolomorphic

open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.SympBase

variable {g : ℕ}

abbrev rc {m n : Type} (M : Matrix m n ℝ) : Matrix m n ℂ := M.map (fun t : ℝ => (t : ℂ))

def numer (γ : Sp g) (τ : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  rc γ.mat.toBlocks₁₁ * τ + rc γ.mat.toBlocks₁₂

theorem moeb_eq (γ : Sp g) (τ : Matrix (Fin g) (Fin g) ℂ) :
    moeb γ τ = numer γ τ * (den γ τ)⁻¹ := rfl

theorem rc_mul_fromRows (γ : Sp g) (τ : Matrix (Fin g) (Fin g) ℂ) :
    rc γ.mat * fromRows τ (1 : Matrix (Fin g) (Fin g) ℂ) = fromRows (numer γ τ) (den γ τ) := by
  have h : rc γ.mat = fromBlocks (rc γ.mat.toBlocks₁₁) (rc γ.mat.toBlocks₁₂)
      (rc γ.mat.toBlocks₂₁) (rc γ.mat.toBlocks₂₂) := by
    ext (i | i) (j | j) <;> rfl
  rw [h, fromBlocks_mul_fromRows]
  simp [numer, den]

theorem rc_symplectic (γ : Sp g) :
    (rc γ.mat)ᵀ * J (Fin g) ℂ * rc γ.mat = J (Fin g) ℂ := by
  have h := SymplecticGroup.mem_iff'.1 γ.2
  have hJ : (J (Fin g) ℝ).map Complex.ofRealHom = J (Fin g) ℂ := by
    ext (i | i) (j | j) <;> simp [J, Matrix.one_apply] <;> split_ifs <;> simp
  have h2 := congrArg (fun M => M.map Complex.ofRealHom) h
  simp only [Matrix.map_mul, hJ] at h2
  exact h2

theorem rc_conjTranspose {m n : Type} (M : Matrix m n ℝ) : (rc M)ᴴ = (rc M)ᵀ := by
  ext i j; simp [rc]

theorem hecke_relation_image (γ : Sp g) (τ : Matrix (Fin g) (Fin g) ℂ) :
    (den γ τ)ᵀ * numer γ τ - (numer γ τ)ᵀ * den γ τ = τ - τᵀ := by
  rw [← GlobalTheory.IndefiniteRowSideFullHecke.PluriharmonicHolomorphic.fromRows_transpose_J_mul_fromRows, ← rc_mul_fromRows, transpose_mul]
  have := GlobalTheory.IndefiniteRowSideFullHecke.PluriharmonicHolomorphic.fromRows_transpose_J_mul_fromRows τ 1
  simp only [transpose_one, Matrix.one_mul, Matrix.mul_one] at this
  rw [← this]
  conv_rhs => rw [← rc_symplectic γ]
  simp only [Matrix.mul_assoc]

theorem rel_H (γ : Sp g) (τ : Matrix (Fin g) (Fin g) ℂ) :
    (den γ τ)ᴴ * numer γ τ - (numer γ τ)ᴴ * den γ τ = τ - τᴴ := by
  rw [← GlobalTheory.IndefiniteRowSideFullHecke.PluriharmonicHolomorphic.form_H, ← rc_mul_fromRows, conjTranspose_mul, rc_conjTranspose]
  have := GlobalTheory.IndefiniteRowSideFullHecke.PluriharmonicHolomorphic.form_H τ 1
  simp only [conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at this
  rw [← this]
  conv_rhs => rw [← rc_symplectic γ]
  simp only [Matrix.mul_assoc]

open ComplexOrder in

theorem isUnit_den (γ : Sp g) {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : IsSiegel τ) :
    IsUnit (den γ τ) := by
  rw [← mulVec_injective_iff_isUnit]
  have hp := (GlobalTheory.IndefiniteRowSideFullHecke.PluriharmonicHolomorphic.posDef_im_iff hτ.1).1 hτ.2
  have : ∀ v, den γ τ *ᵥ v = 0 → v = 0 := by
    intro v hv
    by_contra h0
    have := hp.dotProduct_mulVec_pos h0
    rw [← rel_H γ, smul_mulVec, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hv, mulVec_zero,
      sub_zero, dotProduct_smul, dotProduct_mulVec, ← star_mulVec, hv] at this
    simp at this
  intro a b hab
  exact sub_eq_zero.1 (this _ (by rw [mulVec_sub]; exact sub_eq_zero.2 hab))

open ComplexOrder in

theorem moeb_isSiegel (γ : Sp g) {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : IsSiegel τ) :
    IsSiegel (moeb γ τ) := by
  have hu := isUnit_den γ hτ
  have hd := (isUnit_iff_isUnit_det _).1 hu
  have h1 : den γ τ * (den γ τ)⁻¹ = 1 := mul_nonsing_inv _ hd
  have hT := hecke_relation_image γ τ
  have hH := rel_H γ τ
  rw [moeb_eq]
  set P := numer γ τ
  set Q := den γ τ
  set R := Q⁻¹
  have hs : (P * R).IsSymm := by
    rw [hτ.1.eq, sub_self] at hT
    have h2 : Rᵀ * (Qᵀ * P - Pᵀ * Q) * R = P * R - (P * R)ᵀ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, ← transpose_mul, h1, transpose_one,
        Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one, transpose_mul]
    rw [hT, Matrix.mul_zero, Matrix.zero_mul] at h2
    exact (sub_eq_zero.1 h2.symm).symm
  refine ⟨hs, (GlobalTheory.IndefiniteRowSideFullHecke.PluriharmonicHolomorphic.posDef_im_iff hs).2 ?_⟩
  have h2 : Rᴴ * (Qᴴ * P - Pᴴ * Q) * R = P * R - (P * R)ᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, ← conjTranspose_mul, h1,
      conjTranspose_one, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one,
      conjTranspose_mul]
  have hp := ((GlobalTheory.IndefiniteRowSideFullHecke.PluriharmonicHolomorphic.posDef_im_iff hτ.1).1 hτ.2).conjTranspose_mul_mul_same (B := R)
    (mulVec_injective_iff_isUnit.2 (isUnit_nonsing_inv_iff.2 hu))
  rwa [Matrix.mul_smul, Matrix.smul_mul, ← hH, h2] at hp

section Family

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem differentiableOn_finsetProd {ι : Type} (u : Finset ι) (f : ι → E → ℂ) {s : Set E}
    (h : ∀ i ∈ u, DifferentiableOn ℂ (f i) s) :
    DifferentiableOn ℂ (fun b => ∏ i ∈ u, f i b) s := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using differentiableOn_const (1 : ℂ)
  | insert a u ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem differentiableOn_det {n : Type} [Fintype n] [DecidableEq n] (f : E → Matrix n n ℂ)
    {s : Set E} (hf : ∀ i j, DifferentiableOn ℂ (fun b => f b i j) s) :
    DifferentiableOn ℂ (fun b => (f b).det) s := by
  simp only [Matrix.det_apply']
  exact DifferentiableOn.fun_sum fun σ _ => DifferentiableOn.const_mul
    (differentiableOn_finsetProd Finset.univ (fun i b => f b (σ i) i)
      fun i _ => hf (σ i) i) _

theorem differentiableOn_inv {n : Type} [Fintype n] [DecidableEq n] (f : E → Matrix n n ℂ)
    {s : Set E} (hf : ∀ i j, DifferentiableOn ℂ (fun b => f b i j) s)
    (hu : ∀ b ∈ s, (f b).det ≠ 0) (i j : n) :
    DifferentiableOn ℂ (fun b => (f b)⁻¹ i j) s := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_apply]
  refine DifferentiableOn.mul ((differentiableOn_det f hf).inv hu) ?_
  refine differentiableOn_det (fun b => (f b).updateRow j (Pi.single i 1)) fun k l => ?_
  by_cases h : k = j
  · subst h; simp only [updateRow_self]; exact differentiableOn_const _
  · simp only [updateRow_ne h]; exact hf k l

end Family

theorem main : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ →
    ∀ γ : Sp g, IsPeriodMap B (fun b => moeb γ (τ b)) ∧ (∀ b ∈ B, IsUnit (den γ (τ b))) ∧
      DifferentiableOn ℂ (reframe τ γ) (cov B g) := by
  intro g E _ _ _ B τ hτ γ
  have hu : ∀ b ∈ B, IsUnit (den γ (τ b)) := fun b hb => isUnit_den γ (hτ.2.2 b hb)
  have hden : ∀ i j, DifferentiableOn ℂ (fun b => den γ (τ b) i j) B := by
    intro i j
    simp only [den, Matrix.add_apply, Matrix.mul_apply, Matrix.map_apply]
    exact (DifferentiableOn.fun_sum fun k _ => (hτ.2.1 k j).const_mul _).add
      (differentiableOn_const _)
  have hinv : ∀ i j, DifferentiableOn ℂ (fun b => (den γ (τ b))⁻¹ i j) B :=
    differentiableOn_inv (fun b => den γ (τ b)) hden
      (fun b hb => ((isUnit_iff_isUnit_det _).1 (hu b hb)).ne_zero)
  refine ⟨⟨hτ.1, fun i j => ?_, fun b hb => moeb_isSiegel γ (hτ.2.2 b hb)⟩, hu, ?_⟩
  · simp only [moeb, Matrix.mul_apply, Matrix.add_apply, Matrix.map_apply]
    refine DifferentiableOn.fun_sum fun k _ => DifferentiableOn.mul ?_ (hinv k j)
    exact (DifferentiableOn.fun_sum fun l _ => (hτ.2.1 l k).const_mul _).add
      (differentiableOn_const _)
  · have hfst : Set.MapsTo Prod.fst (cov B g) B := fun P hP => hP.1
    refine DifferentiableOn.prodMk differentiableOn_fst ?_
    rw [differentiableOn_pi]
    intro j
    simp only [Matrix.vecMul, dotProduct]
    refine DifferentiableOn.fun_sum fun k _ => DifferentiableOn.mul ?_ ?_
    · exact (by fun_prop : Differentiable ℂ (fun P : Pt E g => P.2 k)).differentiableOn
    · exact (hinv k j).comp differentiableOn_fst hfst

end GlobalTheory.SympBase
