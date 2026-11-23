import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1

namespace GlobalTheory.IntegralOpen

open IsDedekindDomain NumberField

theorem isOpen_integral (F : Type) [Field F] [NumberField F] :
    IsOpen {a : FiniteAdeleRing (RingOfIntegers F) F |
      ∀ v : HeightOneSpectrum (RingOfIntegers F),
        (a : (w : HeightOneSpectrum (RingOfIntegers F)) → HeightOneSpectrum.adicCompletion F w) v ∈
          HeightOneSpectrum.adicCompletionIntegers F v} :=
  RestrictedProduct.isOpen_forall_mem
    (R := fun w : HeightOneSpectrum (RingOfIntegers F) => HeightOneSpectrum.adicCompletion F w)
    (A := fun w => (HeightOneSpectrum.adicCompletionIntegers F w : Set (HeightOneSpectrum.adicCompletion F w)))
    (fun _ => Valued.isOpen_valuationSubring _)

end GlobalTheory.IntegralOpen
