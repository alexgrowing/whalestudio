import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsOrbitProd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsLevelProjLevelProj

noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FunExt

def lbc : BCRel := fun K L _ _ _ _ _ v u x X =>
  ∃ f : v.adicCompletion K →+* u.adicCompletion L, Continuous f ∧
    (∀ z : K, f (algebraMap K _ z) = algebraMap L _ (algebraMap K L z)) ∧
    letI : Algebra (v.adicCompletion K) (u.adicCompletion L) := f.toAlgebra
    ∀ s : u.adicCompletion L ≃ₐ[v.adicCompletion K] u.adicCompletion L, s ≠ 1 → GlobalTheory.LBC.IsLBCCl s x X

end GlobalTheory.FunExt

end
