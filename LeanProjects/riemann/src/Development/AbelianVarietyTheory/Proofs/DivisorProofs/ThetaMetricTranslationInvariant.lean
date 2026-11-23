import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

namespace GlobalTheory

theorem theta_translate_imag_part {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (x : Fl g) (z : Fin g → ℂ) :
    (fun i => ((z + per τ x) i).im) =
      (fun i => (z i).im) + (fun i => x (Sum.inl i)) ᵥ* (τ.map Complex.im) := by
  ext i
  simp [per, Matrix.vecMul, dotProduct, Complex.im_sum]

theorem thetaMetric_thetaExp_im {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (x : Fl g) (z : Fin g → ℂ) :
    (thetaExp τ x z).im =
      -(((fun i => x (Sum.inl i)) ᵥ* (τ.map Complex.im)) ⬝ᵥ fun i => x (Sum.inl i)) / 2 -
        (fun i => x (Sum.inl i)) ⬝ᵥ fun i => (z i).im := by
  simp [thetaExp, Matrix.vecMul, dotProduct, Complex.im_sum]

theorem thetaMetric_transl_invariant : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ (x : Fl g), ∀ P ∈ cov B g, Real.exp (-2 * π * ((fun i => ((transl τ x P).2 i).im) ⬝ᵥ ((((τ P.1).map Complex.im)⁻¹) *ᵥ fun i => ((transl τ x P).2 i).im))) * ‖Complex.exp (2 * π * Complex.I * thetaExp (τ P.1) x P.2)‖ ^ 2 = Real.exp (-2 * π * ((fun i => (P.2 i).im) ⬝ᵥ ((((τ P.1).map Complex.im)⁻¹) *ᵥ fun i => (P.2 i).im))) := by
  intro g E _ _ B τ hτ x P hP
  have hS := hτ.2.2 P.1 hP.1
  have hU : IsUnit ((τ P.1).map Complex.im).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 hS.2.isUnit
  have hYiY := Matrix.nonsing_inv_mul _ hU
  have hYYi := Matrix.mul_nonsing_inv _ hU
  have hYt : ((τ P.1).map Complex.im)ᵀ = (τ P.1).map Complex.im := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hS.2.1.eq
  have h2 : (transl τ x P).2 = P.2 + per (τ P.1) x := rfl
  rw [h2, theta_translate_imag_part, Complex.norm_exp]
  have hre : (2 * π * Complex.I * thetaExp (τ P.1) x P.2).re =
      -2 * π * (thetaExp (τ P.1) x P.2).im := by
    simp [Complex.mul_re]
  rw [hre, thetaMetric_thetaExp_im, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  set Y : Matrix (Fin g) (Fin g) ℝ := (τ P.1).map Complex.im with hYdef
  set y : Fin g → ℝ := fun i => (P.2 i).im with hy
  set p : Fin g → ℝ := fun i => x (Sum.inl i) with hp
  have k1 : Y⁻¹ *ᵥ (p ᵥ* Y) = p := by
    rw [← Matrix.mulVec_transpose, hYt, Matrix.mulVec_mulVec, hYiY, Matrix.one_mulVec]
  have k2 : (p ᵥ* Y) ⬝ᵥ (Y⁻¹ *ᵥ y) = p ⬝ᵥ y := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hYYi, Matrix.vecMul_one]
  rw [Matrix.mulVec_add, k1, add_dotProduct, dotProduct_add, dotProduct_add, k2,
    dotProduct_comm y p]
  push_cast
  ring

end GlobalTheory
