import Formalism.UnipotentAdelicQuotients.ClassNumberFinite

namespace HeckeCharacterZeroLocus

open NumberField IsDedekindDomain

def UnipotentStrongApprox : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F))
    (hS : IsGroupLocus S),
    (∀ (K : Type) [Field K] [Algebra F K], ∀ g ∈ zeroLocusGL S K,
      ((g : Matrix (Fin n) (Fin n) K) - 1) ^ n = 0) →
    ∀ (x : locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))
      (W : Set (locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))), IsOpen W → x ∈ W →
      ∃ γ : GL (Fin n) F, γ ∈ zeroLocusGL S F ∧ ∃ y ∈ W,
        (y : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) =
          Units.map (RingHom.mapMatrix (algebraMap F (FiniteAdeleRing (𝓞 F) F))).toMonoidHom γ

end HeckeCharacterZeroLocus
