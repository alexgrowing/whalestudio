import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealSharpBounds.Bounds

noncomputable section

open MeasureTheory Matrix

namespace Ad3.LR.B

def mulTwoByThree : M23 →ₗ[ℝ] M3 →ₗ[ℝ] M23 :=
  LinearMap.mk₂ ℝ (fun X M => Matrix.of.symm (Matrix.of X * Matrix.of M))
    (fun X Y M => by ext r c; simp [Matrix.mul_apply, add_mul, Finset.sum_add_distrib])
    (fun a X M => by ext r c; simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc])
    (fun X M N => by ext r c; simp [Matrix.mul_apply, mul_add, Finset.sum_add_distrib])
    (fun a X M => by ext r c; simp [Matrix.mul_apply, Finset.mul_sum, mul_left_comm])

def mulB : M23 →L[ℝ] M3 →L[ℝ] M23 :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (M3 →ₗ[ℝ] M23) ≃ₗ[ℝ] (M3 →L[ℝ] M23)).toLinearMap ∘ₗ mulTwoByThree)

def mulThreeByThree : M3 →ₗ[ℝ] M3 →ₗ[ℝ] M3 :=
  LinearMap.mk₂ ℝ (fun X M => Matrix.of.symm (Matrix.of X * Matrix.of M))
    (fun X Y M => by ext r c; simp [Matrix.mul_apply, add_mul, Finset.sum_add_distrib])
    (fun a X M => by ext r c; simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc])
    (fun X M N => by ext r c; simp [Matrix.mul_apply, mul_add, Finset.sum_add_distrib])
    (fun a X M => by ext r c; simp [Matrix.mul_apply, Finset.mul_sum, mul_left_comm])

def mul3 : M3 →L[ℝ] M3 →L[ℝ] M3 :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (M3 →ₗ[ℝ] M3) ≃ₗ[ℝ] (M3 →L[ℝ] M3)).toLinearMap ∘ₗ mulThreeByThree)

def Rm (M : M3) : M23 →L[ℝ] M23 := mulB.flip M

def minv (M : M3) : M3 := Matrix.of.symm (Matrix.of M)⁻¹

def ell (M : M3) (i j : Fin 3) : M3 →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (((ContinuousLinearMap.proj j).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => Fin 3 → ℝ) i)).comp (mul3 (minv M)))

theorem ell_apply (M : M3) (i j : Fin 3) (m : M3) :
    ell M i j m = ((((Matrix.of M)⁻¹ * Matrix.of m) i j : ℝ) : ℂ) := rfl

theorem norm_ell_le (M : M3) (i j : Fin 3) : ‖ell M i j‖ ≤ ‖mul3‖ * ‖minv M‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun m => ?_
  have h1 : ‖ell M i j m‖ = ‖mul3 (minv M) m i j‖ := by
    rw [ell_apply, Complex.norm_real]; rfl
  rw [h1]
  calc ‖mul3 (minv M) m i j‖ ≤ ‖mul3 (minv M) m i‖ := norm_le_pi_norm _ j
    _ ≤ ‖mul3 (minv M) m‖ := norm_le_pi_norm _ i
    _ ≤ ‖mul3 (minv M)‖ * ‖m‖ := (mul3 (minv M)).le_opNorm m
    _ ≤ ‖mul3‖ * ‖minv M‖ * ‖m‖ := by gcongr; exact mul3.le_opNorm _

def Zx (h : M22) (x : Fin 2 → ℝ) : M23 := Matrix.of.symm (Matrix.of h * blk x)

def Th (h : M22) : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin (Matrix.of h)⁻¹)

end Ad3.LR.B
