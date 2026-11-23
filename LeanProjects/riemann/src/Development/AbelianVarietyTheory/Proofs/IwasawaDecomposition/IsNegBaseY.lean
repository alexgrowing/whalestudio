import Mathlib
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss

variable {P Q : ℕ}

def IsNeg (Y : Matrix (Ix P Q) (Fin Q) ℂ) : Prop := (-(Yᴴ * Jm P Q * Y)).PosDef

def matA (Y : Matrix (Ix P Q) (Fin Q) ℂ) : Matrix (Fin P) (Fin Q) ℂ := Y.toRows₁ * (Y.toRows₂)⁻¹

def linX (Y : Matrix (Ix P Q) (Fin Q) ℂ) (v φ : Ix P Q → ℂ) : Ix P Q → ℂ :=
  Sum.elim (v ∘ Sum.inl - matA Y *ᵥ (v ∘ Sum.inr)) ((φ ∘ Sum.inl) ᵥ* matA Y + φ ∘ Sum.inr)

def scal (Y : Matrix (Ix P Q) (Fin Q) ℂ) (v φ : Ix P Q → ℂ) : ℂ :=
  (Y.toRows₂.det)⁻¹ * Complex.exp (-((linX Y v φ ∘ Sum.inr) ⬝ᵥ (v ∘ Sum.inr)))

def ker (Y : Matrix (Ix P Q) (Fin Q) ℂ) (v φ : Ix P Q → ℂ) (Y' : Matrix (Ix P Q) (Fin Q) ℂ)
    (v' φ' : Ix P Q → ℂ) : ℂ :=
  ((-(Yᴴ * Jm P Q * Y')).det)⁻¹ * Complex.exp ((star v ᵥ* Jm P Q) ⬝ᵥ v' -
    (star v ᵥ* Jm P Q + φ') ⬝ᵥ (Y' * (Yᴴ * Jm P Q * Y')⁻¹ * Yᴴ * Jm P Q) *ᵥ (Jm P Q *ᵥ star φ + v'))

def baseY (A : Matrix (Fin P) (Fin Q) ℂ) : Matrix (Ix P Q) (Fin Q) ℂ := Matrix.fromRows A 1

def baseV (x : Ix P Q → ℂ) : Ix P Q → ℂ := Sum.elim (x ∘ Sum.inl) 0

def baseF (x : Ix P Q → ℂ) : Ix P Q → ℂ := Sum.elim 0 (x ∘ Sum.inr)

def dA (Z : Mat P Q) (A : Matrix (Fin P) (Fin Q) ℂ) : Matrix (Fin P) (Fin Q) ℂ :=
  Z.toBlocks₁₁ * A + Z.toBlocks₁₂ - A * (Z.toBlocks₂₁ * A + Z.toBlocks₂₂)

def dX (Z : Mat P Q) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) : Ix P Q → ℂ :=
  Sum.elim ((Z.toBlocks₁₁ - A * Z.toBlocks₂₁) *ᵥ (x ∘ Sum.inl))
    (-((x ∘ Sum.inr) ᵥ* (Z.toBlocks₂₁ * A + Z.toBlocks₂₂)))

def dS (Z : Mat P Q) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) : ℂ :=
  -(Z.toBlocks₂₁ * A + Z.toBlocks₂₂).trace - (x ∘ Sum.inr) ⬝ᵥ Z.toBlocks₂₁ *ᵥ (x ∘ Sum.inl)

theorem toRows₂_baseY (A : Matrix (Fin P) (Fin Q) ℂ) : (baseY A).toRows₂ = 1 := rfl

theorem matA_baseY (A : Matrix (Fin P) (Fin Q) ℂ) : matA (baseY A) = A := by
  simp [matA, baseY]

theorem linX_base (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) : linX (baseY A) (baseV x) (baseF x) = x := by
  have h1 : baseV x ∘ Sum.inr = 0 := rfl
  have h2 : baseF x ∘ Sum.inl = 0 := rfl
  rw [linX, h1, h2]
  ext (i | j) <;> simp [baseV, baseF]

theorem scal_base (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) : scal (baseY A) (baseV x) (baseF x) = 1 := by
  have h1 : baseV x ∘ Sum.inr = 0 := rfl
  simp [scal, h1, toRows₂_baseY]

theorem form_blocks (Y Y' : Matrix (Ix P Q) (Fin Q) ℂ) :
    -(Yᴴ * Jm P Q * Y') = Y.toRows₂ᴴ * Y'.toRows₂ - Y.toRows₁ᴴ * Y'.toRows₁ := by
  conv_lhs => rw [← Matrix.fromRows_toRows Y, ← Matrix.fromRows_toRows Y']
  rw [Jm, Formalism.UG.Jpq, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks,
    Matrix.fromCols_mul_fromRows]
  simp [sub_eq_add_neg]

theorem frame_eq (Y : Matrix (Ix P Q) (Fin Q) ℂ) (h : IsUnit Y.toRows₂.det) :
    Y = baseY (matA Y) * Y.toRows₂ := by
  rw [baseY, Matrix.fromRows_mul, matA, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h, Matrix.mul_one,
    Matrix.one_mul, Matrix.fromRows_toRows]

theorem form_factor (Y Y' : Matrix (Ix P Q) (Fin Q) ℂ) (h : IsUnit Y.toRows₂.det) (h' : IsUnit Y'.toRows₂.det) :
    -(Yᴴ * Jm P Q * Y') = Y.toRows₂ᴴ * (1 - (matA Y)ᴴ * matA Y') * Y'.toRows₂ := by
  have e : ∀ Y : Matrix (Ix P Q) (Fin Q) ℂ, IsUnit Y.toRows₂.det → matA Y * Y.toRows₂ = Y.toRows₁ := fun Y h => by
    rw [matA, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h, Matrix.mul_one]
  rw [form_blocks, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
    e Y h, Matrix.mul_assoc, e Y' h']

theorem isNeg_baseY {A : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef) : IsNeg (baseY A) := by
  rw [IsNeg, form_blocks]
  simpa [baseY] using h

theorem IsNeg.isUnit {Y : Matrix (Ix P Q) (Fin Q) ℂ} (h : IsNeg Y) : IsUnit Y.toRows₂.det := by
  rw [IsNeg, form_blocks] at h
  have h2 := h.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self Y.toRows₁)
  rw [sub_add_cancel] at h2
  have h3 := h2.isUnit
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at h3
  exact isUnit_of_mul_isUnit_right h3

theorem IsNeg.posDef {Y : Matrix (Ix P Q) (Fin Q) ℂ} (h : IsNeg Y) : (1 - (matA Y)ᴴ * matA Y).PosDef := by
  have hu := h.isUnit
  rw [IsNeg, form_factor Y Y hu hu] at h
  have hu' : IsUnit Y.toRows₂ := (Matrix.isUnit_iff_isUnit_det _).2 hu
  exact (hu'.posDef_star_left_conjugate_iff).1 h

theorem form_mul {g : Mat P Q} (hg : gᴴ * Jm P Q * g = Jm P Q) (Y Y' : Matrix (Ix P Q) (Fin Q) ℂ) :
    (g * Y)ᴴ * Jm P Q * (g * Y') = Yᴴ * Jm P Q * Y' := by
  rw [Matrix.conjTranspose_mul]
  conv_rhs => rw [← hg]
  simp only [Matrix.mul_assoc]

theorem IsNeg.mul {g : Mat P Q} (hg : gᴴ * Jm P Q * g = Jm P Q) {Y : Matrix (Ix P Q) (Fin Q) ℂ} (h : IsNeg Y) :
    IsNeg (g * Y) := by
  rwa [IsNeg, form_mul hg]

theorem Jm_mul_Jm : Jm P Q * Jm P Q = 1 := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem ker_mul {g g' : Mat P Q} (hg : gᴴ * Jm P Q * g = Jm P Q) (hg' : g' * g = 1)
    (Y : Matrix (Ix P Q) (Fin Q) ℂ) (v φ : Ix P Q → ℂ) (Y' : Matrix (Ix P Q) (Fin Q) ℂ) (v' φ' : Ix P Q → ℂ) :
    ker (g * Y) (g *ᵥ v) (φ ᵥ* g') (g * Y') (g *ᵥ v') (φ' ᵥ* g') = ker Y v φ Y' v' φ' := by
  have hg2 : g * g' = 1 := mul_eq_one_comm.1 hg'
  have h1 : gᴴ * Jm P Q = Jm P Q * g' := by
    conv_rhs => rw [← hg, Matrix.mul_assoc, hg2, Matrix.mul_one]
  have h0 : g' = Jm P Q * gᴴ * Jm P Q := by
    rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]
  have hJ : (Jm P Q)ᴴ = Jm P Q := by simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]
  have h2 : Jm P Q * g'ᴴ = g * Jm P Q := by
    rw [h0, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJ, Matrix.conjTranspose_conjTranspose,
      ← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]
  have e1 : star (g *ᵥ v) ᵥ* Jm P Q = (star v ᵥ* Jm P Q) ᵥ* g' := by
    rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, h1]
  have e2 : Jm P Q *ᵥ star (φ ᵥ* g') = g *ᵥ (Jm P Q *ᵥ star φ) := by
    rw [Matrix.star_vecMul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h2]
  have e3 : g * Y' * (Yᴴ * Jm P Q * Y')⁻¹ * (g * Y)ᴴ * Jm P Q =
      g * (Y' * (Yᴴ * Jm P Q * Y')⁻¹ * Yᴴ * Jm P Q) * g' := by
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc, h1]
  have e4 : ∀ (u w : Ix P Q → ℂ) (M : Mat P Q), (u ᵥ* g') ⬝ᵥ (g * M * g') *ᵥ (g *ᵥ w) = u ⬝ᵥ M *ᵥ w := by
    intro u w M
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 2
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hg', Matrix.one_mul, Matrix.mul_assoc, hg', Matrix.mul_one]
  rw [ker, ker, form_mul hg, e1, e2, e3, ← Matrix.add_vecMul, ← Matrix.mulVec_add, e4, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, hg', Matrix.one_mulVec]

end GlobalTheory.OscGauss

end
