import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift

noncomputable section

open MeasureTheory NumberField GlobalTheory.CuspRep
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace

namespace UpperTheory.ConvolutionTheory.BW

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

abbrev onQ (h : GA E r → ℂ) (y : RightCosetSpace (rationalGLOne E r)) : ℂ := h ((Quotient.out y : normOneGL E r) : GA E r)

abbrev muQ (E : Type) [Field E] [NumberField E] (r : ℕ) : Measure (RightCosetSpace (rationalGLOne E r)) :=
  quotientMeasure (rationalGLOne E r) (mu1 E r)

def pr (Φ f : GA E r → ℂ) : ℂ := ∫ y, onQ Φ y * starRingEnd ℂ (onQ f y) ∂muQ E r

def j0 (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r : ℕ) : Module.End ℂ (Sm E r) :=
  ((r * Module.finrank ℚ E : ℕ) : ℂ)⁻¹ • ∑ τ : E →+* ℂ, ∑ i : Fin r, Eop τ i i

end UpperTheory.ConvolutionTheory.BW
