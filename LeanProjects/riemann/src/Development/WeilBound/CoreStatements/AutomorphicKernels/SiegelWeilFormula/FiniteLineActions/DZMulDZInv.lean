import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinOneMulEqZeroIff

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem dZ_mul_dZ_inv (n : ℕ) {ζ : ℂ} (hζ : ζ ≠ 0) : dZ n ζ⁻¹ * dZ n ζ = 1 := by
  simp only [dZ, Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_smul,
    smul_smul, mul_inv_cancel₀ hζ, one_smul, smul_zero, Matrix.fromBlocks_one]

theorem rot_cols' (n m : ℕ) {ζ : ℂ} (hζ : ζ ≠ 0) (s : ℤˣ) (t x y : ℝ) (Ww : Matrix (Fin m) (Fin n) ℂ) (D : M2 n)
    (hD : dZ n ζ * D = yrotM n s t * dZ n ζ) :
    Matrix.fromCols ((y : ℂ) • ((-(((s : ℤ) : ℂ) * ζ)) • Ww)) ((x : ℂ) • Ww) * Dᵀ =
      Matrix.fromCols (((y * Real.cos t - x * Real.sin t : ℝ) : ℂ) • ((-(((s : ℤ) : ℂ) * ζ)) • Ww))
        (((x * Real.cos t + y * Real.sin t : ℝ) : ℂ) • Ww) := by
  have cancel : ∀ X Y : Matrix (Fin m) (Fin n ⊕ Fin n) ℂ, X * (dZ n ζ)ᵀ = Y * (dZ n ζ)ᵀ → X = Y := by
    intro X Y h
    have h2 := congrArg (· * (dZ n ζ⁻¹)ᵀ) h
    simpa only [Matrix.mul_assoc, ← Matrix.transpose_mul, dZ_mul_dZ_inv n hζ, Matrix.transpose_one,
      Matrix.mul_one] using h2
  apply cancel
  rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hD, Matrix.transpose_mul, ← Matrix.mul_assoc]
  simp only [dZ, yrotM, Matrix.fromBlocks_transpose, Matrix.fromCols_mul_fromBlocks, Matrix.mul_one, Matrix.mul_zero,
    Matrix.mul_smul, Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_smul, add_zero, zero_add, smul_smul,
    ← add_smul]
  rcases Int.units_eq_one_or s with rfl | rfl <;>
  · congr 2 <;> push_cast <;> ring

end PositivityTheory.SiegelWeilFormula.KFP

end
