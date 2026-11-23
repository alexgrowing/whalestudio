import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development

open MeasureTheory Polynomial
open PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.NormElem

noncomputable section

section Abstract

variable {G : Type*} [Group G]

end Abstract

section Matrices

variable {F : Type*} [Field F] {n : ℕ}

def DiagGL (g : GL (Fin n) F) : Prop := ∀ i j : Fin n, i ≠ j → (g : Matrix (Fin n) (Fin n) F) i j = 0

theorem matrix_eq_diagonal {M : Matrix (Fin n) (Fin n) F} (h : ∀ i j : Fin n, i ≠ j → M i j = 0) :
    M = Matrix.diagonal (fun i => M i i) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · rw [h i j hij, Matrix.diagonal_apply_ne _ hij]

theorem DiagGL.comm {g g' : GL (Fin n) F} (h : DiagGL g) (h' : DiagGL g') : g * g' = g' * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, matrix_eq_diagonal h, matrix_eq_diagonal h',
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem DiagGL.mul {g g' : GL (Fin n) F} (h : DiagGL g) (h' : DiagGL g') : DiagGL (g * g') := by
  intro i j hij
  rw [Units.val_mul, matrix_eq_diagonal h, matrix_eq_diagonal h', Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_apply_ne _ hij]

end Matrices

section Galois

variable {k E : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] {n : ℕ}

end Galois

end

end GlobalTheory.CompanionTheory.NormElem
