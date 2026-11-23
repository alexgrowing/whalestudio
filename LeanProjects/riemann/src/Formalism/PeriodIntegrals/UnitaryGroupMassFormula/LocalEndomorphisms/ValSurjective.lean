import Mathlib
import Formalism.PeriodIntegrals.LocalEnd

open NumberField IsDedekindDomain

namespace PI.LocalEndW

def HenselRoot : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ℓ : ℕ) (u : v.adicCompletion F),
    Valued.v (ℓ : v.adicCompletion F) = 1 → Valued.v (u - 1) < 1 → ∃ z : v.adicCompletion F, z ^ ℓ = u

def IntPreserved : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (τ : v.adicCompletion F →+* v.adicCompletion F) (x : v.adicCompletion F),
    Valued.v x ≤ 1 → Valued.v (τ x) ≤ 1

def ValPreserved : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (τ : v.adicCompletion F →+* v.adicCompletion F) (x : v.adicCompletion F),
    Valued.v (τ x) = Valued.v x

def IntOfHensel : Prop := HenselRoot → IntPreserved

def ValOfInt : Prop := IntPreserved → ValPreserved

def ValContinuous : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (τ : v.adicCompletion F →+* v.adicCompletion F),
    (∀ x, Valued.v (τ x) = Valued.v x) → Continuous τ

def ValSurjective : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (τ : v.adicCompletion F →+* v.adicCompletion F),
    (∀ x, Valued.v (τ x) = Valued.v x) → Function.Surjective τ

end PI.LocalEndW
