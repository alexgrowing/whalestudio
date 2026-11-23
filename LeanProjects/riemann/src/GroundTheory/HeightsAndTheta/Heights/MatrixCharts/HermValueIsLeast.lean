import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.MCSchur

open Matrix

noncomputable section

def qf {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (u : ι → ℝ) : ℝ := u ⬝ᵥ (A *ᵥ u)

theorem hermValue_eq_qf {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (w : ι → ℂ) :
    hermValue A w = qf A (fun k => (w k).re) + qf A (fun k => (w k).im) := by
  simp only [hermValue, hermPair, qf, dotProduct, mulVec, Matrix.map_apply, Complex.re_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [Pi.star_apply, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
  ring

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem inv_toBlocks₂₂_eq (Y : Matrix (m ⊕ n) (m ⊕ n) ℝ) (hY : IsUnit Y.det)
    (hA : IsUnit (Y⁻¹).toBlocks₁₁.det) :
    (Y.toBlocks₂₂)⁻¹ = (Y⁻¹).toBlocks₂₂ - (Y⁻¹).toBlocks₂₁ * ((Y⁻¹).toBlocks₁₁)⁻¹ * (Y⁻¹).toBlocks₁₂ := by
  set Z := Y⁻¹ with hZ
  have hYZ : Y * Z = 1 := Matrix.mul_nonsing_inv Y hY
  rw [← fromBlocks_toBlocks Y, ← fromBlocks_toBlocks Z, fromBlocks_multiply, ← fromBlocks_one,
    fromBlocks_inj] at hYZ
  obtain ⟨-, -, h21, h22⟩ := hYZ
  apply Matrix.inv_eq_right_inv
  have e : Y.toBlocks₂₁ = -(Y.toBlocks₂₂ * Z.toBlocks₂₁) * (Z.toBlocks₁₁)⁻¹ := by
    have := congrArg (· * (Z.toBlocks₁₁)⁻¹) h21
    simp only [Matrix.add_mul, Matrix.zero_mul] at this
    rw [Matrix.mul_nonsing_inv_cancel_right _ _ hA] at this
    rw [Matrix.neg_mul]
    exact eq_neg_of_add_eq_zero_left this
  rw [Matrix.mul_sub, ← h22, e]
  simp only [Matrix.neg_mul, Matrix.mul_assoc]
  abel

theorem qf_isLeast (Y : Matrix (m ⊕ n) (m ⊕ n) ℝ) (hY : Y.PosDef) (c : n → ℝ) :
    IsLeast (Set.range fun a : m → ℝ => qf Y⁻¹ (Sum.elim a c)) (qf (Y.toBlocks₂₂)⁻¹ c) := by
  have hZ : (Y⁻¹).PosDef := hY.inv
  set Z := Y⁻¹ with hZdef
  have hA : (Z.toBlocks₁₁).PosDef := hZ.submatrix Sum.inl_injective
  have hAu : IsUnit (Z.toBlocks₁₁).det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  have : Invertible Z.toBlocks₁₁ := hA.isUnit.invertible
  have h21 : Z.toBlocks₂₁ = (Z.toBlocks₁₂)ᴴ := by
    ext i j
    have := congrFun (congrFun hZ.1 (Sum.inr i)) (Sum.inl j)
    simpa [Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.conjTranspose_apply] using this.symm
  have hZeq : Z = fromBlocks Z.toBlocks₁₁ Z.toBlocks₁₂ (Z.toBlocks₁₂)ᴴ Z.toBlocks₂₂ := by
    rw [← h21, fromBlocks_toBlocks]
  have hS : (Y.toBlocks₂₂)⁻¹ = Z.toBlocks₂₂ - (Z.toBlocks₁₂)ᴴ * (Z.toBlocks₁₁)⁻¹ * Z.toBlocks₁₂ := by
    rw [inv_toBlocks₂₂_eq Y ((Matrix.isUnit_iff_isUnit_det _).mp hY.isUnit) hAu, h21]
  have key : ∀ a : m → ℝ, qf Z (Sum.elim a c) =
      qf Z.toBlocks₁₁ (a + ((Z.toBlocks₁₁)⁻¹ * Z.toBlocks₁₂) *ᵥ c) + qf (Y.toBlocks₂₂)⁻¹ c := by
    intro a
    have := schur_complement_eq₁₁ (A := Z.toBlocks₁₁) Z.toBlocks₁₂ Z.toBlocks₂₂ a c hA.1
    simp only [star_trivial] at this
    rw [hS, qf, qf, qf, dotProduct_mulVec, dotProduct_mulVec, dotProduct_mulVec, ← this, ← hZeq]
  refine ⟨⟨-(((Z.toBlocks₁₁)⁻¹ * Z.toBlocks₁₂) *ᵥ c), ?_⟩, ?_⟩
  · simp only
    rw [key, neg_add_cancel]
    simp [qf]
  · rintro _ ⟨a, rfl⟩
    simp only
    rw [key]
    have := hA.posSemidef.dotProduct_mulVec_nonneg (a + ((Z.toBlocks₁₁)⁻¹ * Z.toBlocks₁₂) *ᵥ c)
    simp only [star_trivial] at this
    unfold qf
    linarith

theorem hermValue_isLeast (Y : Matrix (m ⊕ n) (m ⊕ n) ℝ) (hY : Y.PosDef) (v : n → ℂ) :
    IsLeast (Set.range fun x : m → ℂ => hermValue Y⁻¹ (Sum.elim x v))
      (hermValue (Y.toBlocks₂₂)⁻¹ v) := by
  have hre := qf_isLeast Y hY (fun k => (v k).re)
  have him := qf_isLeast Y hY (fun k => (v k).im)
  have split : ∀ x : m → ℂ, hermValue Y⁻¹ (Sum.elim x v) =
      qf Y⁻¹ (Sum.elim (fun k => (x k).re) (fun k => (v k).re)) +
        qf Y⁻¹ (Sum.elim (fun k => (x k).im) (fun k => (v k).im)) := by
    intro x
    rw [hermValue_eq_qf]
    congr 2 <;> ext k <;> cases k <;> rfl
  obtain ⟨⟨a, ha⟩, hlre⟩ := hre
  obtain ⟨⟨b, hb⟩, hlim⟩ := him
  refine ⟨⟨fun k => ⟨a k, b k⟩, ?_⟩, ?_⟩
  · simp only at ha hb ⊢
    rw [split, hermValue_eq_qf]
    exact congrArg₂ (· + ·) ha hb
  · rintro _ ⟨x, rfl⟩
    simp only
    rw [split, hermValue_eq_qf]
    exact add_le_add (hlre ⟨_, rfl⟩) (hlim ⟨_, rfl⟩)

theorem schurQuotient : SchurQuotient.Statement := fun _ _ Y hY v => hermValue_isLeast Y hY v

end

end GroundTheory.Heights₂.Heights.MCSchur
