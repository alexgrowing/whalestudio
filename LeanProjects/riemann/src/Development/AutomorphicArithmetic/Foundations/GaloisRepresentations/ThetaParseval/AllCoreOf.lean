import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CoreAtIffRowAt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.GoodLifts.OfIsGood

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.UnitaryBC

namespace UpperTheory.Gal.TP

def InertOK (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), ¬ IsSplitAt w →
    (2 : 𝓞 (maximalRealSubfield E)) ∉ (w.under (𝓞 (maximalRealSubfield E))).asIdeal ∧
      3 < Ideal.absNorm (w.under (𝓞 (maximalRealSubfield E))).asIdeal ∧
      ¬ differentIdeal ℤ (𝓞 (maximalRealSubfield E)) ≤ (w.under (𝓞 (maximalRealSubfield E))).asIdeal

def TwoUpOK : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    (∃ x : E, ∃ d : ℕ, 0 < d ∧ x ^ 2 = -(d : E)) → Even (Module.finrank ℚ (maximalRealSubfield E)) → InertOK E →
    ∀ n : ℕ, 1 ≤ n → Even n → Sub.TwoUp E n

def AllCore : Prop :=
  GlobalTheory.Row9.CoreU → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), GlobalTheory.Row9.FieldOK l E → InertOK E → ∀ n : ℕ, 1 ≤ n → CoreAt E Ω ι n

end UpperTheory.Gal.TP

end
