import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.AI

universe u v

open Module

noncomputable def ordMod {A : Type*} [CommRing A] (p : PrimeSpectrum A) (x : A) : ℕ∞ :=
  Ring.ord (A ⧸ p.asIdeal) (Ideal.Quotient.mk p.asIdeal x)

noncomputable def ordLoc {A : Type*} [CommRing A] (p : PrimeSpectrum A) (x : A) : ℕ∞ :=
  Ring.ord (Localization.AtPrime p.asIdeal) (algebraMap A (Localization.AtPrime p.asIdeal) x)

def LocalLengthAdditivity : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (M : Type v) [AddCommGroup M]
    [Module A M] [Module.Finite A M] (x : A),
    ringKrullDim A = 1 →
    length A (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) ≠ ⊤ →
    length A (LinearMap.ker (LinearMap.lsmul A M x)) ≠ ⊤ ∧
    length A (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) =
      length A (LinearMap.ker (LinearMap.lsmul A M x)) +
        ∑ᶠ (p : PrimeSpectrum A) (_ : ringKrullDim (A ⧸ p.asIdeal) = 1),
          length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) *
            ordMod p x

def LocalLengthAdditivityTorsionFree : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (M : Type v)
    [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.IsTorsionFree A M] (x : A),
    ringKrullDim A = 1 → x ≠ 0 →
    length A (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) = (finrank A M : ℕ∞) * Ring.ord A x

def LocalLengthMultiplicativity : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (a b : A),
    ringKrullDim A = 2 → a ≠ 0 → b ≠ 0 →
    length A (A ⧸ Ideal.span {a, b}) ≠ ⊤ →
    (length A (A ⧸ Ideal.span {a, b}) =
      length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) +
        ∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1 ∧ a ∈ p.asIdeal),
          ordLoc p a * ordMod p b) ∧
    (length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) =
      length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) ∧
     length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) ≠ ⊤) ∧
    (∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1 ∧ a ∈ p.asIdeal), ordLoc p a * ordMod p b) =
      ∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1 ∧ b ∈ p.asIdeal), ordLoc p b * ordMod p a

end ReciprocityTheory.ChartRestriction.G.AI
