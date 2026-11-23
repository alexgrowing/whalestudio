import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsLocExtFinrankEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupRestriction
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

noncomputable section

open scoped Pointwise

namespace GlobalTheory.WeilRestrict

section

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
  [Algebra K Ω] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω]

def liftG (τ : G K Ω) (hτ : ∀ x : L, τ (algebraMap L Ω x) = algebraMap L Ω x) : G L Ω :=
  AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) hτ

@[simp] theorem liftG_apply (τ : G K Ω) (hτ : ∀ x : L, τ (algebraMap L Ω x) = algebraMap L Ω x)
    (z : Ω) : liftG τ hτ z = τ z := rfl

end

end GlobalTheory.WeilRestrict
