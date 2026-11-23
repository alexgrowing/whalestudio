import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.BlockMul

theorem blocks_mul : ∀ {F : Type} [Field F] (r d c e : ℕ) (x : Matrix (Fin (r + d)) (Fin (r + c)) F) (y : Matrix (Fin (r + c)) (Fin (r + e)) F), bAA (x * y) = bAA x * bAA y + bAD x * bDA y ∧ bAD (x * y) = bAA x * bAD y + bAD x * bDD y ∧ bDA (x * y) = bDA x * bAA y + bDD x * bDA y ∧ bDD (x * y) = bDA x * bAD y + bDD x * bDD y := by
  intro F _ r d c e x y
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>
    simp only [bAA, bAD, bDA, bDD, Matrix.submatrix_apply, Matrix.add_apply, Matrix.mul_apply,
      Fin.sum_univ_add]

end GlobalTheory.CompanionTheory.QL.BlockMul
