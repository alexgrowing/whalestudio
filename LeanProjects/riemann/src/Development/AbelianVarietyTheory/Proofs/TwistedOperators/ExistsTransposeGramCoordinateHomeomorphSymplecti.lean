import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAddEquivSymplecticCoordsOrientedModel

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Twist.exists_transposeGram_coordinate_homeomorph_symplectic

variable {D : D7}

theorem gram_map_mul_inv {R : Type*} [CommRing R] (S : HSp D) (φ : D.host.E →+* R) :
    S.gram.map φ * (S.gram⁻¹).map φ = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel.gram_det_ne_zero S)),
    Matrix.map_one _ φ.map_zero φ.map_one]

theorem gram_inv_map_mul {R : Type*} [CommRing R] (S : HSp D) (φ : D.host.E →+* R) :
    (S.gram⁻¹).map φ * S.gram.map φ = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel.gram_det_ne_zero S)),
    Matrix.map_one _ φ.map_zero φ.map_one]

def coordsLin (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank) (e₂ : Fin S'.rank ≃ Fin T.rank) :
    WO S' T' ≃ₗ[AE D] WO S T where
  toFun u := (HMul.hMul (uᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))
  invFun x := ((HMul.hMul x ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂
  map_add' u v := by
    show (u + v)ᵀ.submatrix e₂.symm e₁.symm * _ = uᵀ.submatrix e₂.symm e₁.symm * _ + vᵀ.submatrix e₂.symm e₁.symm * _
    rw [Matrix.transpose_add, ← Matrix.add_mul]
    rfl
  map_smul' c u := by
    show (c • u)ᵀ.submatrix e₂.symm e₁.symm * _ = c • (uᵀ.submatrix e₂.symm e₁.symm * _)
    rw [Matrix.transpose_smul, ← Matrix.smul_mul]
    rfl
  left_inv u := by
    show ((uᵀ.submatrix e₂.symm e₁.symm * S.gram.map (incA D) * (S.gram⁻¹).map (incA D))ᵀ).submatrix e₁ e₂ = u
    rw [Matrix.mul_assoc, gram_map_mul_inv, Matrix.mul_one]
    ext i j; simp
  right_inv x := by
    dsimp only
    have : (((HMul.hMul x ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂)ᵀ.submatrix e₂.symm e₁.symm =
        (HMul.hMul x ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
      ext i j; simp
    rw [this, Matrix.mul_assoc, gram_inv_map_mul, Matrix.mul_one]

theorem map_transpose_submatrix {A B : Type*} [Semiring A] [Semiring B] (φ : A →+* B) {m n p q : Type*}
    (u : Matrix m n A) (f : p → n) (g : q → m) : (uᵀ.submatrix f g).map φ = ((u.map φ)ᵀ).submatrix f g := rfl

theorem coordsLin_map_zero {R : Type*} [Semiring R] (φ : AE D →+* R) (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank)
    (e₂ : Fin S'.rank ≃ Fin T.rank) (x : WO S' T') (h : x.map φ = 0) : (coordsLin S T S' T' e₁ e₂ x).map φ = 0 := by
  change (HMul.hMul (xᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map φ = 0
  rw [Matrix.map_mul, map_transpose_submatrix, h]
  simp

theorem coordsLin_symm_map_zero {R : Type*} [Semiring R] (φ : AE D →+* R) (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank)
    (e₂ : Fin S'.rank ≃ Fin T.rank) (y : WO S T) (h : y.map φ = 0) : ((coordsLin S T S' T' e₁ e₂).symm y).map φ = 0 := by
  change (((HMul.hMul y ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂).map φ = 0
  rw [map_transpose_submatrix, Matrix.map_mul, h]
  simp

theorem coordsLin_map_zero_iff {R : Type*} [Semiring R] (φ : AE D →+* R) (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank)
    (e₂ : Fin S'.rank ≃ Fin T.rank) (x : WO S' T') : (coordsLin S T S' T' e₁ e₂ x).map φ = 0 ↔ x.map φ = 0 := by
  refine ⟨fun h => ?_, coordsLin_map_zero φ S T S' T' e₁ e₂ x⟩
  have := coordsLin_symm_map_zero φ S T S' T' e₁ e₂ _ h
  rwa [LinearEquiv.symm_apply_apply] at this

theorem coordsLin_rat_iff (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank)
    (e₂ : Fin S'.rank ≃ Fin T.rank) (x : WO S' T') : coordsLin S T S' T' e₁ e₂ x ∈ ratL T S ↔ x ∈ ratL T' S' := by
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨((γ * S.gram⁻¹)ᵀ).submatrix e₁ e₂, ?_⟩
    rw [← (coordsLin S T S' T' e₁ e₂).symm_apply_apply x, ← hγ]
    change (((γ * S.gram⁻¹)ᵀ).submatrix e₁ e₂).map (incA D) =
      ((HMul.hMul (γ.map (incA D)) ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂
    rw [map_transpose_submatrix, Matrix.map_mul]
  · rintro ⟨γ, rfl⟩
    refine ⟨γᵀ.submatrix e₂.symm e₁.symm * S.gram, ?_⟩
    change (γᵀ.submatrix e₂.symm e₁.symm * S.gram).map (incA D) =
      (HMul.hMul ((γ.map (incA D))ᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))
    rw [Matrix.map_mul, map_transpose_submatrix]

theorem coordsLin_spec (D : D7) (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank) (e₂ : Fin S'.rank ≃ Fin T.rank) :
    ∃ L : WO S' T' ≃ₗ[AE D] WO S T,
      (∀ u, L u = (HMul.hMul (uᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))) ∧
      (∀ x : Matrix (Fin T.rank) (Fin S.rank) (AE D),
        L.symm x = ((HMul.hMul x ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂) ∧
      Continuous L ∧ Continuous L.symm ∧ (∀ x, L x ∈ ratL T S ↔ x ∈ ratL T' S') ∧
      (∀ x, (L x).map (infPart D) = 0 ↔ x.map (infPart D) = 0) ∧ ∀ x, (L x).map (finPart D) = 0 ↔ x.map (finPart D) = 0 := by
  refine ⟨coordsLin S T S' T' e₁ e₂, fun _ => rfl, fun _ => rfl, ?_, ?_, coordsLin_rat_iff S T S' T' e₁ e₂,
    coordsLin_map_zero_iff _ S T S' T' e₁ e₂, coordsLin_map_zero_iff _ S T S' T' e₁ e₂⟩
  · change Continuous fun u : WO S' T' =>
      (HMul.hMul (uᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))
    exact (continuous_id.matrix_transpose.matrix_submatrix _ _).matrix_mul continuous_const
  · change Continuous fun x : WO S T =>
      ((HMul.hMul x ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂
    exact ((continuous_id.matrix_mul continuous_const).matrix_transpose).matrix_submatrix _ _

end GlobalTheory.Twist.exists_transposeGram_coordinate_homeomorph_symplectic
