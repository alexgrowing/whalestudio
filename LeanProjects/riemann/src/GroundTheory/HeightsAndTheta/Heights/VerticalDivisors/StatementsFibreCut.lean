import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial IsDedekindDomain

def FibreClosedComponent.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDedekindDomain O] (F : Type) [Field F] [Algebra O F]
    [IsFractionRing O F] (n : ℕ) (P W : Ideal (MvPolynomial (Fin n) O)) (v : HeightOneSpectrum O),
    P.IsPrime → P.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥ →
      W ∈ (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal).minimalPrimes →
        W.IsMaximal →
          ringKrullDim (MvPolynomial (Fin n) F ⧸ P.map (MvPolynomial.map (algebraMap O F))) = 0

def FibreCut.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDedekindDomain O] (n : ℕ) (P W : Ideal (MvPolynomial (Fin n) O))
    (v : HeightOneSpectrum O),
    P.IsPrime → P.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥ →
      W ∈ (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal).minimalPrimes →
        ¬ W.IsMaximal →
          ∃ (P' W' : Ideal (MvPolynomial (Fin n) O)) (f : MvPolynomial (Fin n) O),
            f ∉ P ∧ P' ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧
            P'.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥ ∧
            W' ∈ (P' ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal).minimalPrimes ∧
            ringKrullDim (MvPolynomial (Fin n) O ⧸ W') + 1 = ringKrullDim (MvPolynomial (Fin n) O ⧸ W)

def GenericFibreDrop.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] (F : Type) [Field F] [Algebra O F]
    [IsFractionRing O F] (n : ℕ) (P P' : Ideal (MvPolynomial (Fin n) O))
    (f : MvPolynomial (Fin n) O),
    P.IsPrime → P'.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥ → f ∉ P →
      P' ∈ (P ⊔ Ideal.span {f}).minimalPrimes →
        ringKrullDim (MvPolynomial (Fin n) F ⧸ P.map (MvPolynomial.map (algebraMap O F))) =
          ringKrullDim (MvPolynomial (Fin n) F ⧸ P'.map (MvPolynomial.map (algebraMap O F))) + 1

def CodimOnePrimeAvoid.Statement : Prop :=
  ∀ (k B : Type) [Field k] [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B] (h : B),
    h ≠ 0 → 1 ≤ ringKrullDim B →
      ∃ N : Ideal B, N.IsPrime ∧ h ∉ N ∧ ringKrullDim (B ⧸ N) + 1 = ringKrullDim B

def two : HeightOneSpectrum ℤ :=
  ⟨Ideal.span {2}, (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_two, by simp⟩

end GroundTheory.Heights₂.Heights.Vertical
