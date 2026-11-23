import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapApply

set_option autoImplicit false

open Matrix MeasureTheory Set GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped ContDiff

namespace GlobalTheory.TorsionForm

theorem per_vecMul_symplectic_mat {g : ℕ} (γ : Sp g) (T : Matrix (Fin g) (Fin g) ℂ) (y : Fl g) :
    per T (y ᵥ* γ.mat) =
      (fun i => (y (Sum.inl i) : ℂ)) ᵥ*
        (γ.mat.toBlocks₁₁.map (fun t : ℝ => (t : ℂ)) * T +
          γ.mat.toBlocks₁₂.map (fun t : ℝ => (t : ℂ))) +
      (fun i => (y (Sum.inr i) : ℂ)) ᵥ* den γ T := by
  have hp : (fun i => (((y ᵥ* γ.mat) (Sum.inl i) : ℝ) : ℂ)) =
      (fun i => (y (Sum.inl i) : ℂ)) ᵥ* γ.mat.toBlocks₁₁.map (fun t : ℝ => (t : ℂ)) +
      (fun i => (y (Sum.inr i) : ℂ)) ᵥ* γ.mat.toBlocks₂₁.map (fun t : ℝ => (t : ℂ)) := by
    funext i
    simp [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₁₁, Matrix.toBlocks₂₁]
  have hq : (fun i => (((y ᵥ* γ.mat) (Sum.inr i) : ℝ) : ℂ)) =
      (fun i => (y (Sum.inl i) : ℂ)) ᵥ* γ.mat.toBlocks₁₂.map (fun t : ℝ => (t : ℂ)) +
      (fun i => (y (Sum.inr i) : ℂ)) ᵥ* γ.mat.toBlocks₂₂.map (fun t : ℝ => (t : ℂ)) := by
    funext i
    simp [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂]
  unfold per den
  rw [hp, hq, Matrix.add_vecMul, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, Matrix.vecMul_add,
    Matrix.vecMul_add]
  abel

theorem per_vecMul_den_inv_eq_per_moeb {g : ℕ} (γ : Sp g) (T : Matrix (Fin g) (Fin g) ℂ)
    (x : Fl g) (hu : IsUnit (den γ T)) :
    per T x ᵥ* (den γ T)⁻¹ = per (moeb γ T) (x ᵥ* (γ⁻¹).mat) := by
  have h1 : (γ⁻¹).mat * γ.mat = 1 := congrArg Subtype.val (inv_mul_cancel γ)
  have hx : x = (x ᵥ* (γ⁻¹).mat) ᵥ* γ.mat := by
    rw [Matrix.vecMul_vecMul, h1, Matrix.vecMul_one]
  generalize x ᵥ* (γ⁻¹).mat = y at hx
  subst hx
  rw [per_vecMul_symplectic_mat, Matrix.add_vecMul, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu), Matrix.vecMul_one]
  rfl

end GlobalTheory.TorsionForm
