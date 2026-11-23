import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FibreIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenbasisBaseChange

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FlatRow

namespace GlobalTheory.IntegralEigFrame

open Matrix

section Lie

variable {R K O : Type} [CommRing R] [CommRing K] [CommRing O]

end Lie

theorem exists_char {E L : Type} [Field E] [Field L] [NumberField L] (𝔓 : HeightOneSpectrum (𝓞 L)) (τ : E →+* L) :
    ∃ χ : 𝓞 E →+* AdelicDegreeTameRamification.valRing L 𝔓,
      (algebraMap (AdelicDegreeTameRamification.valRing L 𝔓) L).comp χ = τ.comp (algebraMap (𝓞 E) E) :=
  ⟨(τ.comp (algebraMap (𝓞 E) E)).codRestrict (AdelicDegreeTameRamification.valRing L 𝔓) fun z =>
    𝔓.valuation_le_one (K := L) (RingOfIntegers.mapRingHom τ z), rfl⟩

end GlobalTheory.IntegralEigFrame
