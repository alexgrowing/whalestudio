import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
open Matrix GlobalTheory.PELU
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)

namespace GlobalTheory.PeriodCoord

private theorem inv_mul_eq_mul_inv_of_intertwine {n : Type} [Fintype n] [DecidableEq n]
    (A B D : Matrix n n ℂ) (hA : A.det ≠ 0) (hD : D.det ≠ 0) (h : B * D = A * B) :
    A⁻¹ * B = B * D⁻¹ := by
  have hA' : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hD' : IsUnit D.det := isUnit_iff_ne_zero.mpr hD
  calc A⁻¹ * B = A⁻¹ * (B * D) * D⁻¹ := by
          rw [Matrix.mul_assoc A⁻¹, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hD', Matrix.mul_one]
    _ = A⁻¹ * A * B * D⁻¹ := by rw [h, Matrix.mul_assoc A⁻¹ A B]
    _ = B * D⁻¹ := by rw [Matrix.nonsing_inv_mul _ hA', Matrix.one_mul]

private theorem star_dot_mulVec {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) (x y : Fin g → ℂ) :
    star (x ⬝ᵥ A *ᵥ y) = star x ⬝ᵥ A.map star *ᵥ star y := by
  simp [dotProduct, mulVec, star_sum, Finset.mul_sum]

private theorem star_mulVec' {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) (y : Fin g → ℂ) :
    star (A *ᵥ y) = A.map star *ᵥ star y := by
  funext i
  simp [mulVec, dotProduct, star_sum]

private theorem dot_left {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) (x y : Fin g → ℂ) :
    (A *ᵥ x) ⬝ᵥ y = x ⬝ᵥ Aᵀ *ᵥ y := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]

private theorem map_star_mul' {g : ℕ} (A B : Matrix (Fin g) (Fin g) ℂ) :
    (A * B).map star = A.map star * B.map star := by
  ext i j; simp [Matrix.mul_apply, star_sum]

private theorem map_star_map_star' {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) : (A.map star).map star = A := by
  ext i j; simp

private theorem conj_transpose_intertwine {g : ℕ} (M₀ C : Matrix (Fin g) (Fin g) ℂ) (hH : M₀ᴴ = M₀)
    (hS : (Cᵀ * M₀)ᵀ = Cᵀ * M₀) : (C.map star)ᵀ * Cᵀ * M₀ = M₀ * C.map star * C := by
  have f0 : M₀.map star = M₀ᵀ := by
    ext i j
    have := congrFun (congrFun hH j) i
    simpa [conjTranspose_apply] using this
  have f1 : M₀ᵀ * C = Cᵀ * M₀ := by rw [transpose_mul, transpose_transpose] at hS; exact hS
  have f1' : M₀ * C.map star = (C.map star)ᵀ * M₀ᵀ := by
    have := congrArg (fun A => A.map star) f1
    simp only [map_star_mul'] at this
    have e1 : (M₀ᵀ).map star = M₀ := by rw [transpose_map, f0, transpose_transpose]
    have e2 : (Cᵀ).map star = (C.map star)ᵀ := by rw [transpose_map]
    rw [e1, e2, f0] at this
    exact this
  rw [Matrix.mul_assoc, ← f1, ← Matrix.mul_assoc, ← f1']

theorem riemann_converse {g : ℕ} (M₀ C : Matrix (Fin g) (Fin g) ℂ) (hH : M₀ᴴ = M₀) (_hdet : M₀.det ≠ 0)
    (hS : (Cᵀ * M₀)ᵀ = Cᵀ * M₀) (hY : (1 - C.map star * C).det ≠ 0) :
    (M₀ * (1 - C.map star * C)⁻¹)ᴴ = M₀ * (1 - C.map star * C)⁻¹ ∧
      ∀ z w : Fin g → ℂ, (hermForm (M₀ * (1 - C.map star * C)⁻¹) (z + C *ᵥ star z) (w + C *ᵥ star w)).im =
        (hermForm M₀ z w).im := by
  set Y := 1 - C.map star * C with hYdef
  set M := M₀ * Y⁻¹ with hMdef
  have f2 := conj_transpose_intertwine M₀ C hH hS
  have f1 : M₀ᵀ * C = Cᵀ * M₀ := by rw [transpose_mul, transpose_transpose] at hS; exact hS
  have hYh : Yᴴ = 1 - (C.map star)ᵀ * Cᵀ := by
    rw [hYdef, conjTranspose_sub, conjTranspose_one, conjTranspose_mul]
    congr 2
    · ext i j; simp
  have hYt : Yᵀ = 1 - Cᵀ * (C.map star)ᵀ := by
    rw [hYdef, transpose_sub, transpose_one, transpose_mul]

  have ha : Mᴴ = M := by
    rw [hMdef, conjTranspose_mul, conjTranspose_nonsing_inv, hH]
    apply inv_mul_eq_mul_inv_of_intertwine _ _ _ _ hY
    · rw [hYh, hYdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, f2, Matrix.mul_assoc]
    · rw [det_conjTranspose]; exact star_ne_zero.mpr hY

  have hMbar : M.map star = Mᵀ := by
    ext i j
    have := congrFun (congrFun ha j) i
    simpa [conjTranspose_apply] using this
  have hb : M.map star * C = Cᵀ * M := by
    rw [hMbar, hMdef, transpose_mul, transpose_nonsing_inv, Matrix.mul_assoc, f1, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc]
    rw [Matrix.mul_assoc]
    apply inv_mul_eq_mul_inv_of_intertwine _ _ _ _ hY
    · rw [hYt, hYdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
        Matrix.mul_assoc Cᵀ (C.map star)ᵀ, ← Matrix.mul_assoc (C.map star)ᵀ, f2]
      simp only [Matrix.mul_assoc]
    · rw [det_transpose]; exact hY

  have hc : M = M₀ + (C.map star)ᵀ * M.map star * C := by
    have hYu : IsUnit Y.det := isUnit_iff_ne_zero.mpr hY
    rw [Matrix.mul_assoc, hb, ← Matrix.mul_assoc, hMdef, ← Matrix.mul_assoc, f2]
    have h0 : M₀ = M₀ * Y * Y⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hYu, Matrix.mul_one]
    calc M₀ * Y⁻¹ = (M₀ * Y + M₀ * C.map star * C) * Y⁻¹ := by
          rw [Matrix.mul_assoc M₀ (C.map star), ← Matrix.mul_add, hYdef, sub_add_cancel, Matrix.mul_one]
      _ = M₀ * Y * Y⁻¹ + M₀ * C.map star * C * Y⁻¹ := Matrix.add_mul _ _ _
      _ = _ := by rw [← h0]
  refine ⟨ha, fun z w => ?_⟩
  have e : hermForm M (z + C *ᵥ star z) (w + C *ᵥ star w) =
      z ⬝ᵥ M *ᵥ star w + z ⬝ᵥ (M * C.map star) *ᵥ w + star z ⬝ᵥ (Cᵀ * M) *ᵥ star w
        + star z ⬝ᵥ (Cᵀ * M * C.map star) *ᵥ w := by
    simp only [hermForm, star_add, star_mulVec', star_star, add_dotProduct, mulVec_add, dotProduct_add,
      dot_left, mulVec_mulVec, Matrix.mul_assoc]
    ring
  have e2 : star (z ⬝ᵥ (M * C.map star) *ᵥ w) = star z ⬝ᵥ (Cᵀ * M) *ᵥ star w := by
    rw [star_dot_mulVec, map_star_mul', map_star_map_star', hb]
  have e4 : star (star z ⬝ᵥ (Cᵀ * M * C.map star) *ᵥ w) = z ⬝ᵥ ((C.map star)ᵀ * M.map star * C) *ᵥ star w := by
    rw [star_dot_mulVec, map_star_mul', map_star_mul', map_star_map_star', star_star, transpose_map]
  have e1 : z ⬝ᵥ M *ᵥ star w = hermForm M₀ z w + z ⬝ᵥ ((C.map star)ᵀ * M.map star * C) *ᵥ star w := by
    conv_lhs => rw [hc]
    rw [hermForm, add_mulVec, dotProduct_add]
  rw [e, e1, ← e2, ← e4]
  simp only [Complex.add_im, Complex.star_def, Complex.conj_im]
  ring

end GlobalTheory.PeriodCoord
