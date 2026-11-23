import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafShortComplexExactIffLocallyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.QisSec

variable {R : Type} [CommRing R]

abbrev secF (U : Scheme.{0}) : Shv R ⥤ ModuleCat.{1} (ULift.{1} R) :=
  sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U)

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 U P Q h hPQ

section Cone
variable {K L : Cx R} (f : K ⟶ L) {U : Scheme.{0}}

end Cone

section Main
variable {K L : Cx R} (f : K ⟶ L)

end Main

end GlobalTheory.EtC.QisSec

namespace GlobalTheory.EtC

end GlobalTheory.EtC
