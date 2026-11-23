import Mathlib
import Formalism.DistinguishedUnitIdeals.Statement

noncomputable section

namespace Formalism.ExponentWindows

def SatDist : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (d : ℕ) (p : PowerSeries O), UnitDist ϖ d p →
      ∀ (k N : ℕ) (z : PowerSeries O), PowerSeries.C (ϖ ^ N) * z ∈ Ideal.span {p ^ k} →
        z ∈ Ideal.span {p ^ k}

def ConstDist : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (d : ℕ) (p : PowerSeries O), UnitDist ϖ d p → 1 ≤ d →
      ∀ (c : O) (y N : ℕ) (a : PowerSeries O),
        PowerSeries.C (ϖ ^ N) * (PowerSeries.C c - PowerSeries.C (ϖ ^ y) * a) ∈ Ideal.span {p} →
        ϖ ^ y ∣ c

def CoprimeProd : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (d d' : ℕ) (p p' : PowerSeries O), UnitDist ϖ d p → UnitDist ϖ d' p' → CoprimeRat ϖ p p' →
      ∀ (a b : ℕ) (z : PowerSeries O), z ∈ Ideal.span {p ^ a} → z ∈ Ideal.span {p' ^ b} →
        z ∈ Ideal.span {p ^ a * p' ^ b}

end Formalism.ExponentWindows
