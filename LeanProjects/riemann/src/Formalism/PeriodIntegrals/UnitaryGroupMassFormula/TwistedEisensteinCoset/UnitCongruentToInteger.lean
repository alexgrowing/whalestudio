import Formalism.PeriodIntegrals.TwistedEisensteinNonvanishing

open NumberField IsDedekindDomain

noncomputable section

namespace PI.TwistedEisensteinNonvanishing.W

def IntegerIntegralIffDvd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ∀ i e : ℕ, IntAt P ((i : E) / (qOf P : E) ^ e) ↔ qOf P ^ e ∣ i

def IntegralApproximationByInteger : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ∀ (x : E) (N : ℕ), IntAt P x → ∃ i : ℕ, i < qOf P ^ N ∧ IntAt P ((x - i) / (qOf P : E) ^ N)

def ElementEqPrimePowerMulUnit : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ∀ a : E, a ≠ 0 → ∃ (e : ℤ) (w : E), a = (qOf P : E) ^ e * w ∧ w ≠ 0 ∧ IntAt P w ∧ IntAt P w⁻¹

def ValuationExponentUnique : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ∀ (e e' : ℤ) (w w' : E), w ≠ 0 → IntAt P w → IntAt P w⁻¹ → IntAt P w' → IntAt P w'⁻¹ →
      (qOf P : E) ^ e * w = (qOf P : E) ^ e' * w' → e = e'

def UnitCongruentToInteger : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ∀ (w : E) (N : ℕ), w ≠ 0 → IntAt P w → IntAt P w⁻¹ →
      ∃ w0 : ℕ, Nat.Coprime w0 (qOf P) ∧ IntAt P ((w - w0) / (qOf P : E) ^ N)

end PI.TwistedEisensteinNonvanishing.W
