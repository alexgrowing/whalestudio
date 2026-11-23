import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Lbc

noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open GlobalTheory.FunExt

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

def ArthurClozelStrongSupp : Prop := StrongBC lbc

end GlobalTheory.Published

end
