import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EpsMeasFamily

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

open GlobalTheory.LocLanglands

def DeligneLocalConstants : Prop :=
  ∀ (Ω : Type) [Field Ω] (A : ValuationSubring Ω), ∃ ε : EpsMeasFamily A, IsDeligneMeas ε

end GlobalTheory.Published

end
