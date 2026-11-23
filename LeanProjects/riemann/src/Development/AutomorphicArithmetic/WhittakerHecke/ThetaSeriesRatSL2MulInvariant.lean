import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.BddInt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem vm_mul_inv (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) (x : Fin 2 → ℚ) :
    (x ᵥ* γ.1) ᵥ* (γ⁻¹).1 = x := by
  rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]

private theorem vm_inv_mul (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) (x : Fin 2 → ℚ) :
    (x ᵥ* (γ⁻¹).1) ᵥ* γ.1 = x := by
  rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]

private def rowE (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) : Rw ℚ ≃ Rw ℚ where
  toFun ξ := ⟨ξ.1 ᵥ* γ.1, fun h => ξ.2 (by
    have := vm_mul_inv γ ξ.1
    rw [h, Matrix.zero_vecMul] at this
    exact this.symm)⟩
  invFun ξ := ⟨ξ.1 ᵥ* (γ⁻¹).1, fun h => ξ.2 (by
    have := vm_inv_mul γ ξ.1
    rw [h, Matrix.zero_vecMul] at this
    exact this.symm)⟩
  left_inv ξ := Subtype.ext (vm_mul_inv γ ξ.1)
  right_inv ξ := Subtype.ext (vm_inv_mul γ ξ.1)

private theorem row_rat (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) (x : Fin 2 → ℚ) :
    (fun i => rt (x i)) ᵥ* (ratS ℚ γ).1 = fun i => rt ((x ᵥ* γ.1) i) := by
  funext j
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, ratS, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Matrix.map_apply, map_add, map_mul]

theorem UpperTheory.thetaSeries_ratSL2_mul_invariant :
    ∀ (Φ : (Fin 2 → A ℚ) → ℂ) (t : ℝ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) (g : G1 ℚ) (h : GL (Fin 2) (A ℚ)),
        ThR Φ t (gl (ratS ℚ γ * g) * h) = ThR Φ t (gl g * h) := by
  intro Φ t γ g h
  unfold ThR
  rw [← (rowE γ).tsum_eq (fun ξ : Rw ℚ => Φ fun j => (iy (Real.exp t) : A ℚ) * ((fun i => rt (ξ.1 i)) ᵥ* (gl g * h).val) j)]
  refine tsum_congr fun ξ => ?_
  have key : (fun i => rt (ξ.1 i)) ᵥ* (gl (ratS ℚ γ * g) * h).val
      = (fun i => rt ((rowE γ ξ).1 i)) ᵥ* (gl g * h).val := by
    have e : (gl (ratS ℚ γ * g) * h).val = (ratS ℚ γ).1 * (gl g * h).val := by
      simp [gl, Matrix.SpecialLinearGroup.toGL, Matrix.mul_assoc]
    rw [e, ← Matrix.vecMul_vecMul, row_rat]
    rfl
  rw [key]
