import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdLawAtOfSteps
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryOneFiniteAdelicOfDetNormOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.H90RangeEqNormOneOfIsQuad
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.TwU.IntegralHilbert90
open GlobalTheory.AdeleBaseChange
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def evP (P : HeightOneSpectrum (𝓞 E)) : FiniteAdeleRing (𝓞 E) E →+* P.adicCompletion E where
  toFun z := z P
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem localComponent_apply₂ (P : HeightOneSpectrum (𝓞 E)) (z : FiniteAdeleRing (𝓞 E) E) : evP P z = z P := rfl

theorem localComponent_algebraMap (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    evP P (algebraMap E (FiniteAdeleRing (𝓞 E) E) x) = algebraMap E (P.adicCompletion E) x := rfl

variable [StarRing E]

end GlobalTheory.TwU.IntegralHilbert90
