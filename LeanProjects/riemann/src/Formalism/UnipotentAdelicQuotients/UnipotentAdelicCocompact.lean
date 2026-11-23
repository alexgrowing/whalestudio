import Formalism.UnipotentAdelicQuotients.ClassNumberFinite

namespace HeckeCharacterZeroLocus

open NumberField IsDedekindDomain

def UnipotentAdelicCocompact : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F))
    (hS : IsGroupLocus S),
    (∀ (K : Type) [Field K] [Algebra F K], ∀ g ∈ zeroLocusGL S K,
      ((g : Matrix (Fin n) (Fin n) K) - 1) ^ n = 0) →
    ∃ C : Set (locusSubgroup S hS (AdeleRing (𝓞 F) F)), IsCompact C ∧
      ∀ x : locusSubgroup S hS (AdeleRing (𝓞 F) F), ∃ γ : GL (Fin n) F, γ ∈ zeroLocusGL S F ∧ ∃ c ∈ C,
        (x : GL (Fin n) (AdeleRing (𝓞 F) F)) =
          Units.map (RingHom.mapMatrix (algebraMap F (AdeleRing (𝓞 F) F))).toMonoidHom γ *
            (c : GL (Fin n) (AdeleRing (𝓞 F) F))

end HeckeCharacterZeroLocus
