import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsIntegralPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open IsDedekindDomain NumberField

noncomputable section

def IntegralPointOfAlgebraicDomain.Hyp (F : Type) [Field F] [NumberField F] (S : Type) [CommRing S]
    [Algebra (𝓞 F) S] (v : HeightOneSpectrum (𝓞 F)) (M : Ideal S) : Prop :=
  Function.Injective (algebraMap (𝓞 F) S) ∧ Algebra.IsAlgebraic (𝓞 F) S ∧ M.IsMaximal ∧
    M.comap (algebraMap (𝓞 F) S) = v.asIdeal

def IntegralPointOfAlgebraicDomain.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Type) [CommRing S] [IsDomain S] [Algebra (𝓞 F) S]
    [Algebra.FiniteType (𝓞 F) S] (v : HeightOneSpectrum (𝓞 F)) (M : Ideal S),
    IntegralPointOfAlgebraicDomain.Hyp F S v M →
    ∃ (L : Type) (_ : Field L) (_ : Algebra (v.adicCompletion F) L)
      (_ : FiniteDimensional (v.adicCompletion F) L) (y : S →+* L),
      y.comp (algebraMap (𝓞 F) S) =
          (algebraMap (v.adicCompletion F) L).comp
            ((algebraMap F (v.adicCompletion F)).comp (algebraMap (𝓞 F) F)) ∧
        Function.Injective y ∧
        (∀ a : S, (completionIntegersTo F v L).IsIntegralElem (y a)) ∧
        (∀ a ∉ M, ∃ b : L, b * y a = 1 ∧ (completionIntegersTo F v L).IsIntegralElem b) ∧
        ∀ a ∈ M, ∀ b : L, b * y a = 1 → ¬ (completionIntegersTo F v L).IsIntegralElem b

end

end GroundTheory.Heights₂.Heights.FourB
