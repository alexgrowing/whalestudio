import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ComapLiftFormConstChartPrimeExample
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def LocalizedQuotLength.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (P : Ideal S) (W₀ : Ideal (S ⧸ P)) [W₀.IsPrime] (z : S),
    Module.length (Localization.AtPrime (W₀.comap (Ideal.Quotient.mk P)))
        (LocalizedModule (W₀.comap (Ideal.Quotient.mk P)).primeCompl (S ⧸ (P ⊔ Ideal.span {z}))) =
      Module.length (Localization.AtPrime W₀)
        (Localization.AtPrime W₀ ⧸
          Ideal.span {algebraMap (S ⧸ P) (Localization.AtPrime W₀) (Ideal.Quotient.mk P z)})

def LengthMapIdealLe.Statement : Prop :=
  ∀ (C D : Type u) [CommRing C] [CommRing D] [IsLocalRing D] (φ : C →+* D),
    (∀ m : Ideal C, m.IsMaximal → m.map φ = ⊤ ∨ IsLocalRing.maximalIdeal D ≤ m.map φ) →
    ∀ I : Ideal C, Module.length D (D ⧸ I.map φ) ≤ Module.length C (C ⧸ I)

def IntermediateRingQuotLength.Statement : Prop :=
  ∀ (A C : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing C] [IsDomain C]
    [Algebra A C], ringKrullDim A = 1 → Function.Injective (algebraMap A C) →
    (∀ c : C, ∃ a : A, a ≠ 0 ∧ a • c ∈ Set.range (algebraMap A C)) →
    ∀ a : A, a ≠ 0 →
      Module.length A (C ⧸ Ideal.span {algebraMap A C a}) ≤ Module.length A (A ⧸ Ideal.span {a})

def BlowUpLocalChart.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (J : Type) [Fintype J] (P : Ideal (MRing ι R)), P.IsPrime →
    ∀ (u : J → MRing ι R) (G' : Ideal (MRing (extIdx ι J) R)) (y : MRing (extIdx ι J) R),
      y ∉ blowUpOf P u → G' ∈ (blowUpOf P u ⊔ Ideal.span {y}).minimalPrimes → IsRelevant G' →
    ∀ x : MRing ι R, x ∉ P → G'.comap (liftForm (J := J)) ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
    ∀ (G₀ : Ideal (MRing ι R ⧸ P)) [G₀.IsPrime],
      G₀.comap (Ideal.Quotient.mk P) = G'.comap (liftForm (J := J)) →
    ∀ (W₀ : Ideal (MRing (extIdx ι J) R ⧸ blowUpOf P u)) [W₀.IsPrime],
      W₀.comap (Ideal.Quotient.mk (blowUpOf P u)) = G' →
    ∃ (C : Subring (Localization.AtPrime W₀)) (f : Localization.AtPrime G₀ →+* C),
      Function.Injective f ∧ (∀ c : C, ∃ a, a ≠ 0 ∧ f a * c ∈ Set.range f) ∧
      (∀ s : MRing ι R,
        (f (algebraMap (MRing ι R ⧸ P) (Localization.AtPrime G₀) (Ideal.Quotient.mk P s)) :
            Localization.AtPrime W₀) =
          algebraMap (MRing (extIdx ι J) R ⧸ blowUpOf P u) (Localization.AtPrime W₀)
            (Ideal.Quotient.mk (blowUpOf P u) (liftForm s))) ∧
      IsLocalRing.maximalIdeal (Localization.AtPrime W₀) ≤
        ((IsLocalRing.maximalIdeal (Localization.AtPrime W₀)).comap C.subtype).map C.subtype

end Lemmas

section Examples

theorem BlowUpLocalChart.exists_quotient_primes {R : Type*} [CommRing R] {K : Type*} {ι : K → Type}
    {J : Type} {P : Ideal (MRing ι R)} {u : J → MRing ι R} {G' : Ideal (MRing (extIdx ι J) R)}
    (hG' : G'.IsPrime) (hQ : blowUpOf P u ≤ G') (hP : P ≤ G'.comap (liftForm (J := J))) :
    ∃ (G₀ : Ideal (MRing ι R ⧸ P)) (W₀ : Ideal (MRing (extIdx ι J) R ⧸ blowUpOf P u)),
      G₀.IsPrime ∧ W₀.IsPrime ∧ G₀.comap (Ideal.Quotient.mk P) = G'.comap (liftForm (J := J)) ∧
        W₀.comap (Ideal.Quotient.mk (blowUpOf P u)) = G' := by
  refine ⟨(G'.comap (liftForm (J := J))).map (Ideal.Quotient.mk P), G'.map (Ideal.Quotient.mk _),
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker]),
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker]),
    Ideal.comap_map_mk hP, Ideal.comap_map_mk hQ⟩

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
