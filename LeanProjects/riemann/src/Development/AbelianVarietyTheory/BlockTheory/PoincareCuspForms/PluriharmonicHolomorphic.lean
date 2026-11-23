import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.PeriodLattice

noncomputable section

open Matrix Topology
open ReciprocityTheory.PTheta

namespace GlobalTheory.IndefiniteRowSideFullHecke.PluriharmonicHolomorphic

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def SymMat (ι : Type) : Submodule ℂ (ι → ι → ℂ) where
  carrier := {x | ∀ i j, x i j = x j i}
  add_mem' := fun {a b} ha hb i j => by simp [ha i j, hb i j]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c a ha i j => by simp [ha i j]

def chart (τ : SiegelH ι) : SymMat ι :=
  ⟨fun i j => τ.1 i j, fun i j => τ.2.1.apply j i⟩

def CDifferentiableAt (F : SiegelH ι → ℂ) (τ : SiegelH ι) : Prop :=
  ∃ G : SymMat ι → ℂ, DifferentiableAt ℂ G (chart τ) ∧ ∀ᶠ σ in 𝓝 τ, F σ = G (chart σ)

def HolomorphicOn (F : SiegelH ι → ℂ) (U : Set (SiegelH ι)) : Prop :=
  ∀ τ ∈ U, CDifferentiableAt F τ

def Holomorphic (F : SiegelH ι → ℂ) : Prop := HolomorphicOn F Set.univ

def Pluriharmonic (u : SiegelH ι → ℝ) : Prop :=
  ∀ τ : SiegelH ι, ∃ U : Set (SiegelH ι), IsOpen U ∧ τ ∈ U ∧
    ∃ H : SiegelH ι → ℂ, HolomorphicOn H U ∧ ∀ σ ∈ U, u σ = (H σ).re

def cx {m n : Type} (M : Matrix m n ℤ) : Matrix m n ℂ := M.map (Int.cast : ℤ → ℂ)

def num (γ : Matrix.symplecticGroup ι ℤ) (τ : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  cx γ.1.toBlocks₁₁ * τ + cx γ.1.toBlocks₁₂

def denom (γ : Matrix.symplecticGroup ι ℤ) (τ : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  cx γ.1.toBlocks₂₁ * τ + cx γ.1.toBlocks₂₂

theorem cx_mul_fromRows (γ : Matrix.symplecticGroup ι ℤ) (τ : Matrix ι ι ℂ) :
    cx γ.1 * fromRows τ (1 : Matrix ι ι ℂ) = fromRows (num γ τ) (denom γ τ) := by
  have h : cx γ.1 = fromBlocks (cx γ.1.toBlocks₁₁) (cx γ.1.toBlocks₁₂) (cx γ.1.toBlocks₂₁)
      (cx γ.1.toBlocks₂₂) := by
    ext (i | i) (j | j) <;> rfl
  rw [h, fromBlocks_mul_fromRows]
  simp [num, denom]

theorem cx_symplectic (γ : Matrix.symplecticGroup ι ℤ) :
    (cx γ.1)ᵀ * J ι ℂ * cx γ.1 = J ι ℂ := by
  have h := SymplecticGroup.mem_iff'.1 γ.2
  have hJ : (J ι ℤ).map (Int.castRingHom ℂ) = J ι ℂ := by
    ext (i | i) (j | j) <;> simp [J, Matrix.one_apply]
  have h2 := congrArg (fun M => M.map (Int.castRingHom ℂ)) h
  simp only [Matrix.map_mul, hJ] at h2
  exact h2

theorem cx_conjTranspose {m n : Type} (M : Matrix m n ℤ) : (cx M)ᴴ = (cx M)ᵀ := by
  ext i j; simp [cx]

theorem fromRows_transpose_J_mul_fromRows (P Q : Matrix ι ι ℂ) :
    (fromRows P Q)ᵀ * J ι ℂ * fromRows P Q = Qᵀ * P - Pᵀ * Q := by
  rw [transpose_fromRows, J, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  simp [sub_eq_add_neg]

theorem form_H (P Q : Matrix ι ι ℂ) :
    (fromRows P Q)ᴴ * J ι ℂ * fromRows P Q = Qᴴ * P - Pᴴ * Q := by
  rw [conjTranspose_fromRows_eq_fromCols_conjTranspose, J, fromCols_mul_fromBlocks,
    fromCols_mul_fromRows]
  simp [sub_eq_add_neg]

theorem hecke_relation_image (γ : Matrix.symplecticGroup ι ℤ) (τ : Matrix ι ι ℂ) :
    (denom γ τ)ᵀ * num γ τ - (num γ τ)ᵀ * denom γ τ = τ - τᵀ := by
  rw [← fromRows_transpose_J_mul_fromRows, ← cx_mul_fromRows, transpose_mul]
  have := fromRows_transpose_J_mul_fromRows τ 1
  simp only [transpose_one, Matrix.one_mul, Matrix.mul_one] at this
  rw [← this]
  conv_rhs => rw [← cx_symplectic γ]
  simp only [Matrix.mul_assoc]

theorem rel_H (γ : Matrix.symplecticGroup ι ℤ) (τ : Matrix ι ι ℂ) :
    (denom γ τ)ᴴ * num γ τ - (num γ τ)ᴴ * denom γ τ = τ - τᴴ := by
  rw [← form_H, ← cx_mul_fromRows, conjTranspose_mul, cx_conjTranspose]
  have := form_H τ 1
  simp only [conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at this
  rw [← this]
  conv_rhs => rw [← cx_symplectic γ]
  simp only [Matrix.mul_assoc]

open ComplexOrder in
omit [DecidableEq ι] in
theorem posDef_ofReal_iff {Y : Matrix ι ι ℝ} (h : Y.IsSymm) :
    (Y.map Complex.ofReal).PosDef ↔ Y.PosDef := by
  have key : ∀ x : ι → ℂ, star x ⬝ᵥ (Y.map Complex.ofReal *ᵥ x) =
      (((fun i => (x i).re) ⬝ᵥ (Y *ᵥ fun i => (x i).re) +
        (fun i => (x i).im) ⬝ᵥ (Y *ᵥ fun i => (x i).im) : ℝ) : ℂ) := by
    intro x
    apply Complex.ext
    · simp [dotProduct, mulVec, Finset.mul_sum, ← Finset.sum_add_distrib]
    · simp only [dotProduct, mulVec, Finset.mul_sum, Complex.im_sum, Complex.ofReal_im,
        Complex.mul_im, Pi.star_apply, map_apply, Complex.star_def, Complex.conj_re,
        Complex.conj_im, Complex.mul_re, Complex.ofReal_re, zero_mul, add_zero, sub_zero,
        Finset.sum_add_distrib, neg_mul, Finset.sum_neg_distrib]
      rw [Finset.sum_comm, add_neg_eq_zero]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [h.apply i j]; ring
  have hY : Y.IsHermitian := by
    ext i j; simp [h.apply i j]
  rw [posDef_iff_dotProduct_mulVec, posDef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨-, H⟩
    refine ⟨hY, fun x hx => ?_⟩
    have hx' : (fun i => (x i : ℂ)) ≠ 0 := by
      intro e; apply hx; ext i; simpa using congrFun e i
    have := H hx'
    rw [key, Complex.zero_lt_real] at this
    simpa [dotProduct, mulVec] using this
  · rintro ⟨-, H⟩
    have H0 : ∀ y : ι → ℝ, 0 ≤ y ⬝ᵥ (Y *ᵥ y) := by
      intro y
      by_cases hy : y = 0
      · simp [hy]
      · simpa using (H hy).le
    refine ⟨?_, fun x hx => ?_⟩
    · ext i j; simp [h.apply i j]
    · rw [key, Complex.zero_lt_real]
      by_cases h1 : (fun i => (x i).re) = 0
      · have h2 : (fun i => (x i).im) ≠ 0 := by
          intro h2; apply hx; ext i
          exact Complex.ext (congrFun h1 i) (congrFun h2 i)
        exact add_pos_of_nonneg_of_pos (H0 _) (by simpa using H h2)
      · exact add_pos_of_pos_of_nonneg (by simpa using H h1) (H0 _)

open ComplexOrder in
omit [DecidableEq ι] in

theorem posDef_im_iff {τ : Matrix ι ι ℂ} (h : τ.IsSymm) :
    (τ.map Complex.im).PosDef ↔ ((-Complex.I / 2) • (τ - τᴴ)).PosDef := by
  have e : (-Complex.I / 2) • (τ - τᴴ) = (τ.map Complex.im).map (Complex.ofReal) := by
    ext i j
    have := h.apply i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, conjTranspose_apply, map_apply, this,
      smul_eq_mul]
    apply Complex.ext <;> simp
    ring
  rw [e, posDef_ofReal_iff (h.map _)]

open ComplexOrder in

theorem isUnit_denom (γ : Matrix.symplecticGroup ι ℤ) (τ : SiegelH ι) : IsUnit (denom γ τ.1) := by
  rw [← mulVec_injective_iff_isUnit]
  have hp := (posDef_im_iff τ.2.1).1 τ.2.2
  have : ∀ v, denom γ τ.1 *ᵥ v = 0 → v = 0 := by
    intro v hv
    by_contra h0
    have := hp.dotProduct_mulVec_pos h0
    rw [← rel_H γ, smul_mulVec, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hv, mulVec_zero,
      sub_zero, dotProduct_smul, dotProduct_mulVec, ← star_mulVec, hv] at this
    simp at this
  intro a b hab
  exact sub_eq_zero.1 (this _ (by rw [mulVec_sub]; exact sub_eq_zero.2 hab))

open ComplexOrder in
theorem act_mem (γ : Matrix.symplecticGroup ι ℤ) (τ : SiegelH ι) :
    num γ τ.1 * (denom γ τ.1)⁻¹ ∈ SiegelH ι := by
  have hu := isUnit_denom γ τ
  have hd := (isUnit_iff_isUnit_det _).1 hu
  have h1 : denom γ τ.1 * (denom γ τ.1)⁻¹ = 1 := mul_nonsing_inv _ hd
  have hT := hecke_relation_image γ τ.1
  have hH := rel_H γ τ.1
  set P := num γ τ.1
  set Q := denom γ τ.1
  set R := Q⁻¹
  have hs : (P * R).IsSymm := by
    rw [τ.2.1.eq, sub_self] at hT
    have h2 : Rᵀ * (Qᵀ * P - Pᵀ * Q) * R = P * R - (P * R)ᵀ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, ← transpose_mul, h1, transpose_one,
        Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one, transpose_mul]
    rw [hT, Matrix.mul_zero, Matrix.zero_mul] at h2
    exact (sub_eq_zero.1 h2.symm).symm
  refine ⟨hs, (posDef_im_iff hs).2 ?_⟩
  have h2 : Rᴴ * (Qᴴ * P - Pᴴ * Q) * R = P * R - (P * R)ᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, ← conjTranspose_mul, h1,
      conjTranspose_one, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one,
      conjTranspose_mul]
  have hp := ((posDef_im_iff τ.2.1).1 τ.2.2).conjTranspose_mul_mul_same (B := R)
    (mulVec_injective_iff_isUnit.2 (isUnit_nonsing_inv_iff.2 hu))
  rwa [Matrix.mul_smul, Matrix.smul_mul, ← hH, h2] at hp

def act (γ : Matrix.symplecticGroup ι ℤ) (τ : SiegelH ι) : SiegelH ι :=
  ⟨num γ τ.1 * (denom γ τ.1)⁻¹, act_mem γ τ⟩

def SpInvariant {α : Type} (u : SiegelH ι → α) : Prop :=
  ∀ (γ : Matrix.symplecticGroup ι ℤ) (τ : SiegelH ι), u (act γ τ) = u τ

def InvariantPluriharmonicConstant : Prop :=
  ∀ g : ℕ, 2 ≤ g → ∀ u : SiegelH (Fin g) → ℝ, Pluriharmonic u → SpInvariant u →
    ∃ c : ℝ, ∀ τ, u τ = c

end GlobalTheory.IndefiniteRowSideFullHecke.PluriharmonicHolomorphic
