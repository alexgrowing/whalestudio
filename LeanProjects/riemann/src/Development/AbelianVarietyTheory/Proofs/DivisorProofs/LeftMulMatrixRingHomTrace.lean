import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem transposedRegularRep_ringHom_trace :
    ∀ (O : Type) [CommRing O] (R Λ : Type) [CommRing R] [CommRing Λ] [Algebra R Λ] (n : ℕ)
      (b : Module.Basis (Fin n) R Λ) (φ : R →+* O),
      (∃ ρ : Λ →+* Matrix (Fin n) (Fin n) O,
        ⇑ρ = fun a : Λ => ((Algebra.leftMulMatrix b a).transpose).map φ) ∧
      ∀ a : Λ, (((Algebra.leftMulMatrix b a).transpose).map φ).trace
        = φ (Algebra.trace R Λ a) := by
  intro O _ R Λ _ _ _ n b φ
  refine ⟨⟨{ toFun := fun a => ((Algebra.leftMulMatrix b a).transpose).map φ
             map_one' := ?_
             map_mul' := ?_
             map_zero' := ?_
             map_add' := ?_ }, rfl⟩, ?_⟩
  · rw [map_one, Matrix.transpose_one]
    exact Matrix.map_one φ (map_zero φ) (map_one φ)
  · intro x y
    rw [mul_comm x y, map_mul, Matrix.transpose_mul, Matrix.map_mul]
  · ext i j
    simp
  · intro x y
    rw [map_add, Matrix.transpose_add]
    ext i j
    simp
  · intro a
    rw [Algebra.trace_eq_matrix_trace b a, ← Matrix.trace_transpose (Algebra.leftMulMatrix b a)]
    simp [Matrix.trace, map_sum]

end GlobalTheory
