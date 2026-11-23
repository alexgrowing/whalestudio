import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.GL2LocalData

theorem tinv_mul' {F : Type} [Field F] {n : Type} [Fintype n] [DecidableEq n] (h g : GL n F) :
    tinv (h * g) = tinv h * tinv g := by
  apply Units.ext
  change ((h * g)⁻¹ : GL n F).valᵀ = (h⁻¹ : GL n F).valᵀ * (g⁻¹ : GL n F).valᵀ
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

end GlobalTheory.CompanionTheory.GL2LocalData
