import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.GaussLam

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

def gTil (E : Type) [CommRing E] [Algebra F E] (g : F → ℂ) (x : F) : ℂ :=
  g (-x⁻¹) * nsg E (-x) * (((modulus x : ℝ)⁻¹ : ℝ) : ℂ)

def hAvg [MeasurableSpace F] [BorelSpace F] (E : Type) [CommRing E] [Algebra F E]
    (χ : AddChar F Circle) (g : F → ℂ) (t : F) : ℂ :=
  ∫ a, g a * nsg E a * (((modulus a : ℝ)⁻¹ : ℝ) : ℂ) * (χ (-t / a) : ℂ) ∂selfDualMeasure χ

end GlobalTheory.CompanionTheory.GaussLam
