import Mathlib

noncomputable section

namespace Formalism.TruncatedSeriesCounting.R9

open PowerSeries

def LengthQuotientLeOfPowSMul : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] (M : Type) [AddCommGroup M]
    [Module O M] [Module.Free O M] [Module.Finite O M] (ℓ : O) (e e' : ℕ) (FFs J : Submodule O M),
    Ideal.span {ℓ ^ e} • FFs ≤ J → Ideal.span {ℓ ^ e'} • (⊤ : Submodule O M) ≤ J →
    Module.length O (M ⧸ J) ≤
      Module.length O (M ⧸ (FFs ⊔ Ideal.span {ℓ ^ e'} • (⊤ : Submodule O M))) +
        ((Module.finrank O M * e : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ})

def CancelQ : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (a : O) (η b : ℕ) (g : PowerSeries O),
    (X : PowerSeries O) ^ η * g ∈ Ideal.span {C a, (X : PowerSeries O) ^ (b + η)} →
      g ∈ Ideal.span {C a, (X : PowerSeries O) ^ b}

def CancelC : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (a : O) (v t b : ℕ) (g : PowerSeries O), a ≠ 0 → v ≤ t →
    C (a ^ v) * g ∈ Ideal.span {C (a ^ t), (X : PowerSeries O) ^ b} →
      g ∈ Ideal.span {C (a ^ (t - v)), (X : PowerSeries O) ^ b}

def TruncZero : Prop :=
  ∀ (R : Type) [CommRing R] (u π₀ q : R) (ℓ M η y : ℕ), M ≤ y → η ≤ (ℓ - 1) * y →
    (u * π₀ * q ^ (ℓ - 1)) ^ y ∈ Ideal.span {π₀ ^ M * q ^ η}

end Formalism.TruncatedSeriesCounting.R9
