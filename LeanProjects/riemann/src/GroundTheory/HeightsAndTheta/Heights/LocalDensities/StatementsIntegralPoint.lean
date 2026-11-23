import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open IsDedekindDomain NumberField

noncomputable section

abbrev completionIntegersTo (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (L : Type) [Field L] [Algebra (v.adicCompletion F) L] : v.adicCompletionIntegers F →+* L :=
  (algebraMap (v.adicCompletion F) L).comp (v.adicCompletionIntegers F).subtype

def IntegralPointThroughPrime.Hyp (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R]
    [Algebra (𝓞 F) R] (v : HeightOneSpectrum (𝓞 F)) (P : Ideal R) (u g : R) : Prop :=
  P.IsPrime ∧ P.comap (algebraMap (𝓞 F) R) = v.asIdeal ∧ u ∉ P ∧ g ≠ 0

def IntegralPointThroughPrime.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R] [IsDomain R] [Algebra (𝓞 F) R]
    [Module.Flat (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R] (v : HeightOneSpectrum (𝓞 F))
    (P : Ideal R) (u g : R), IntegralPointThroughPrime.Hyp F R v P u g →
    ∃ (L : Type) (_ : Field L) (_ : Algebra (v.adicCompletion F) L)
      (_ : FiniteDimensional (v.adicCompletion F) L) (y : R →+* L),
      y.comp (algebraMap (𝓞 F) R) =
          (algebraMap (v.adicCompletion F) L).comp
            ((algebraMap F (v.adicCompletion F)).comp (algebraMap (𝓞 F) F)) ∧
        (∀ a : R, (completionIntegersTo F v L).IsIntegralElem (y a)) ∧
        y g ≠ 0 ∧
        (∃ b : L, b * y u = 1 ∧ (completionIntegersTo F v L).IsIntegralElem b) ∧
        ∀ a ∈ P, ∀ b : L, b * y a = 1 → ¬ (completionIntegersTo F v L).IsIntegralElem b

def placeTwo : HeightOneSpectrum (𝓞 ℚ) :=
  Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩

end

end GroundTheory.Heights₂.Heights.FourB
