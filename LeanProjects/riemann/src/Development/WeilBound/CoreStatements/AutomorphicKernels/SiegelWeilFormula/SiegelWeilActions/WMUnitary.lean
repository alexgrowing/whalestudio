import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.DMEqDiag
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IncMTranspose
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ExistsSigmaNe

noncomputable section

open scoped TensorProduct Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace PositivityTheory.SiegelWeilFormula.Act.CL

section Alg

variable {R : Type} [CommRing R] {n : ℕ} (i₀ : Fin n)

theorem wM_map {S : Type} [CommRing S] (f : R →+* S) (a b : R) : (wM i₀ a b).map f = wM i₀ (f a) (f b) := by
  delta wM
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.single_apply, map_add, map_sub]
  split_ifs <;> simp

theorem wM_blocks (a b : R) : wM i₀ a b = Matrix.fromBlocks (1 - Matrix.single i₀ i₀ 1) (a • Matrix.single i₀ i₀ 1)
    (b • Matrix.single i₀ i₀ 1) (1 - Matrix.single i₀ i₀ 1) := by
  delta wM
  ext (i | i) (j | j) <;>
    simp [Matrix.single_apply, Matrix.one_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

theorem wM_unitary (f : R →+* R) (a b e : R) (h1 : b * e * f a = 1) (h2 : a * f b = e) :
    (wM i₀ a b)ᵀ * kunf.jw n e * (wM i₀ a b).map f = kunf.jw n e := by
  have hjw : kunf.jw n e = Matrix.fromBlocks 0 1 (e • 1) 0 := rfl
  have hEE : Matrix.single i₀ i₀ (1 : R) * Matrix.single i₀ i₀ 1 = Matrix.single i₀ i₀ 1 := by
    rw [Matrix.single_mul_single_same, mul_one]
  have hET : (Matrix.single i₀ i₀ (1 : R))ᵀ = Matrix.single i₀ i₀ 1 := Matrix.transpose_single _ _ _
  have h1' : e * b * f a = 1 := by rw [mul_comm e b]; exact h1
  rw [wM_map, wM_blocks, wM_blocks, hjw]
  generalize Matrix.single i₀ i₀ (1 : R) = E at hEE hET ⊢
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_inj]
  simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hET,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_sub, Matrix.sub_mul, hEE, sub_self, smul_zero,
    sub_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · trivial
  · linear_combination (norm := module) h1' • E
  · linear_combination (norm := module) h2 • E
  · trivial
end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end PositivityTheory.SiegelWeilFormula.Act.CL

end
