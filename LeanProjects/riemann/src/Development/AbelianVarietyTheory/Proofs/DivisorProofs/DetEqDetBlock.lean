import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl

theorem det_eq_det_block : ∀ (g' r g : ℕ) (σ : Fin g ≃ Fin g' ⊕ Fin r) (Mx : Matrix (Fin g) (Fin g) ℂ) (MB : Matrix (Fin g') (Fin g') ℂ), (∀ i, zP σ (Mx (σ.symm (Sum.inl i))) = MB i) → (∀ l, zP σ (Mx (σ.symm (Sum.inr l))) = 0 ∧ tP σ (Mx (σ.symm (Sum.inr l))) = Pi.single l 1) → Mx.det = MB.det := by
  intro g' r g σ Mx MB h1 h2
  have key : Mx.submatrix σ.symm σ.symm =
      Matrix.fromBlocks MB (Matrix.of fun i l => Mx (σ.symm (Sum.inl i)) (σ.symm (Sum.inr l))) 0 1 := by
    ext (i | i) (j | j)
    · exact congrFun (h1 i) j
    · rfl
    · exact congrFun (h2 i).1 j
    · have := congrFun (h2 i).2 j
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
      rw [Pi.single_apply] at this
      simp only [eq_comm (a := i)]
      exact this
  rw [← Matrix.det_submatrix_equiv_self σ.symm Mx, key, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, _root_.mul_one]

end GlobalTheory.MBLow.Cl
