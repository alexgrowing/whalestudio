import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef

noncomputable section

open ValuativeRel IsDedekindDomain NumberField

namespace PI.TrDualLoc

def Stmt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) [Fact (Formalism.MainNotions.S.Loc.resChar p).Prime]
    (Fp : Type) [Field Fp] [ValuativeRel Fp] [TopologicalSpace Fp] [IsNonarchimedeanLocalField Fp]
    [Algebra ℚ_[Formalism.MainNotions.S.Loc.resChar p] Fp], Continuous (algebraMap ℚ_[Formalism.MainNotions.S.Loc.resChar p] Fp) →
    FiniteDimensional ℚ_[Formalism.MainNotions.S.Loc.resChar p] Fp → ∀ (ι : K →+* Fp), DenseRange ι →
    (∀ x y : K, (ι x ≤ᵥ ι y) ↔ p.valuation K x ≤ p.valuation K y) →
    ∀ t : K, (∀ a : 𝓞 K, ∃ n : ℤ, Algebra.trace ℚ K (t * a) = n) →
    ∀ c ∈ 𝒪[Fp], ‖Algebra.trace ℚ_[Formalism.MainNotions.S.Loc.resChar p] Fp (c * ι t)‖ ≤ 1

end PI.TrDualLoc
