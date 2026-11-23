import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.InertialTypesAlt

def BaseCase : Prop :=
  ∀ (K Ω : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field Ω] [Algebra K Ω] (n : ℕ) (π : CuspSub K n)
    (A : ValuationSubring Ω) (Θ : IsLocalRing.ResidueField A →* ℂ) (v : HeightOneSpectrum (𝓞 K)) e e',
    ResEmb A v e → ResEmb A v e' → ∀ τ τ', π.IsLocComp v τ → π.IsLocComp v τ' →
    ∀ a : Lbl, HasLbl (Θ.comp e.toMonoidHom) τ.ρ a → HasLbl (Θ.comp e'.toMonoidHom) τ'.ρ a

end UpperTheory.Gal.InertialTypesAlt
