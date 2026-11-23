import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc

noncomputable section
namespace GlobalTheory.CartanLip
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius

section
variable {n : Type} [Fintype n] [DecidableEq n]

theorem frob_sq (A : Matrix n n ℂ) : ‖A‖ ^ 2 = ∑ a, ∑ b, ‖A a b‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  simp

theorem frob_sq_trace (A : Matrix n n ℂ) : ‖A‖ ^ 2 = (Matrix.trace (A * Aᴴ)).re := by
  rw [frob_sq]
  simp [Matrix.trace, Matrix.mul_apply, Complex.sq_norm, Complex.normSq_apply]

theorem frob_unitary (U A V : Matrix n n ℂ) (hU : Uᴴ * U = 1) (hV : V * Vᴴ = 1) :
    ‖U * A * V‖ = ‖A‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), frob_sq_trace, frob_sq_trace]
  congr 1
  calc trace (U * A * V * (U * A * V)ᴴ) = trace (U * (A * (V * Vᴴ) * Aᴴ * Uᴴ)) := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = trace (A * Aᴴ * (Uᴴ * U)) := by
        rw [hV, trace_mul_comm]; simp only [Matrix.mul_assoc, Matrix.one_mul]
    _ = _ := by rw [hU, Matrix.mul_one]

theorem exp_skew (X : Matrix n n ℂ) (hX : Xᴴ = -X) :
    (NormedSpace.exp X)ᴴ * NormedSpace.exp X = 1 ∧ NormedSpace.exp X * (NormedSpace.exp X)ᴴ = 1 := by
  rw [← Matrix.exp_conjTranspose, hX]
  constructor
  · rw [← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_left]; simp
  · rw [← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_right]; simp

theorem norm_exp_mul_exp_sub_one (X Y : Matrix n n ℂ) (hX : Xᴴ = -X) (hY : Yᴴ = -Y) :
    ‖NormedSpace.exp X * NormedSpace.exp Y - 1‖ ≤ ‖X + Y‖ := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun t : ℝ => NormedSpace.exp (t • X) * NormedSpace.exp (t • Y))
    (f' := fun t : ℝ => NormedSpace.exp (t • X) * (X + Y) * NormedSpace.exp (t • Y)) (C := ‖X + Y‖)
    (fun t _ => by
      have h1 := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X t).fun_mul
        (hasDerivAt_exp_smul_const' (𝕂 := ℝ) Y t)
      refine (h1.congr_deriv ?_).hasDerivWithinAt
      rw [mul_add, add_mul, mul_assoc _ Y]
      rfl)
    (fun t _ => le_of_eq (frob_unitary _ _ _
      (exp_skew _ (by simp [hX])).1 (exp_skew _ (by simp [hY])).2))
  simpa using h

theorem sum_sq_le (H H' : Matrix n n ℂ) (hH : Hᴴ = H) (hH' : H'ᴴ = H') :
    ∑ a, ∑ b, ‖(NormedSpace.exp (-(Complex.I • H')) * NormedSpace.exp (Complex.I • H) - 1) a b‖ ^ 2 ≤
      ∑ a, ∑ b, ‖(H - H') a b‖ ^ 2 := by
  rw [← frob_sq, ← frob_sq]
  have h := norm_exp_mul_exp_sub_one (-(Complex.I • H')) (Complex.I • H)
    (by simp [hH']) (by simp [hH])
  have e : -(Complex.I • H') + Complex.I • H = Complex.I • (H - H') := by
    rw [smul_sub]; abel
  rw [e, norm_smul, Complex.norm_I, one_mul] at h
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

end

theorem exp_mul_exp_sub_one_le : ∀ (p q : ℕ) (H H' : Mat p q), Hᴴ = H → H'ᴴ = H' → ∑ a, ∑ b, ‖(NormedSpace.exp (-(Complex.I • H')) * NormedSpace.exp (Complex.I • H) - 1) a b‖ ^ 2 ≤ ∑ a, ∑ b, ‖(H - H') a b‖ ^ 2 :=
  fun _ _ H H' hH hH' => sum_sq_le H H' hH hH'

end GlobalTheory.CartanLip
