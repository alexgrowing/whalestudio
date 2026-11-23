import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReQuad
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.ThetaMet
open scoped Real ContDiff

noncomputable section
namespace GlobalTheory.ThetaMetInv

theorem theta_metric_invariance {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (hτ : GlobalTheory.IsSiegel τ)
    (l : Fl g) (z : Fin g → ℂ) :
    Real.exp (-2 * π * ((fun i => ((z + per τ l) i).im) ⬝ᵥ (((τ.map Complex.im)⁻¹) *ᵥ
      fun i => ((z + per τ l) i).im))) *
      ‖Complex.exp (2 * π * Complex.I * thetaExp τ l z)‖ ^ 2 =
    Real.exp (-2 * π * ((fun i => (z i).im) ⬝ᵥ (((τ.map Complex.im)⁻¹) *ᵥ
      fun i => (z i).im))) := by
  set Y : Matrix (Fin g) (Fin g) ℝ := τ.map Complex.im with hY
  set y : Fin g → ℝ := fun i => (z i).im with hy
  set p : Fin g → ℝ := fun i => l (Sum.inl i) with hp
  have hYs : Yᵀ = Y := by
    ext i j; simp [hY, ← hτ.1.apply i j]
  have hdet : IsUnit Y.det := (hτ.2.det_pos).ne'.isUnit
  have hinv : Y⁻¹ * Y = 1 := Matrix.nonsing_inv_mul Y hdet
  have hinv' : Y * Y⁻¹ = 1 := Matrix.mul_nonsing_inv Y hdet
  have him : (fun i => ((z + per τ l) i).im) = y + p ᵥ* Y := by
    ext i
    simp [per, hy, hp, hY, Matrix.vecMul, dotProduct, Complex.im_sum]
  have hw : Y⁻¹ *ᵥ (p ᵥ* Y) = p := by
    rw [← Matrix.mulVec_transpose, hYs, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hth : (2 * π * Complex.I * thetaExp τ l z).re =
      2 * π * ((p ᵥ* Y) ⬝ᵥ p) / 2 + 2 * π * (p ⬝ᵥ y) := by
    simp [thetaExp, hy, hp, hY, Matrix.vecMul, dotProduct, Complex.im_sum, Complex.re_sum,
      Complex.mul_re, Complex.mul_im]
    ring
  have hq : (y + p ᵥ* Y) ⬝ᵥ (Y⁻¹ *ᵥ (y + p ᵥ* Y)) =
      y ⬝ᵥ (Y⁻¹ *ᵥ y) + 2 * (p ⬝ᵥ y) + (p ᵥ* Y) ⬝ᵥ p := by
    rw [Matrix.mulVec_add, hw, add_dotProduct, dotProduct_add, dotProduct_add]
    have h1 : (p ᵥ* Y) ⬝ᵥ (Y⁻¹ *ᵥ y) = p ⬝ᵥ y := by
      rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]
    rw [h1, dotProduct_comm y p]
    ring
  rw [him, hq, Complex.norm_exp, hth, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  push_cast
  ring

end GlobalTheory.ThetaMetInv
