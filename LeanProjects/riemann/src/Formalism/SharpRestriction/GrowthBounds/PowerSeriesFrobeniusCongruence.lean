import Formalism.SharpRestriction.GrowthBounds.MixedCoefficientClosed

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace SelfConjCharts

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def ee (i j : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j

def inV (j : Fin 2) (f : PowerSeries C) : MvPowerSeries (Fin 2) C :=
  PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 2) C) f

def HH (X : RawChart C d I κ) (x z : κ → PowerSeries C) : MvPowerSeries (Fin 2) C :=
  hAt X (fun i => inV 0 (x i)) (fun i => inV 1 (z i))

def rs (j : Fin 2) (c : C) : MvPowerSeries (Fin 2) C →+* MvPowerSeries (Fin 2) C :=
  MvPowerSeries.rescale (fun i => if i = j then c else 1)

def rc (c : C) (γ : κ → PowerSeries C) : κ → PowerSeries C := fun i => PowerSeries.rescale c (γ i)

def pw (n : ℕ) (δ : κ → PowerSeries C) : κ → PowerSeries C :=
  fun i => PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ n) (δ i)

end SelfConjCharts

open SelfConjCharts

def PowerSeriesFrobeniusCongruence : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (σ : Type) (f : MvPowerSeries σ C), IntS V f → ∀ μ : σ →₀ ℕ,
    V.MM (MvPowerSeries.coeff (V.l • μ) (f ^ V.l) - MvPowerSeries.coeff μ f ^ V.l)

def RootsOfUnityProductCongruence : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (ζ : C), ζ ^ V.l = 1 → ∀ (j : Fin 2) (f : MvPowerSeries (Fin 2) C), IntS V f →
    ∀ μ, V.MM (MvPowerSeries.coeff μ (∏ k ∈ Finset.range V.l, rs j (ζ ^ k) f - f ^ V.l))

def ExpLowOrderTruncation : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (F : MvPowerSeries (Fin 2) C) (m : ℕ), 1 ≤ m →
    (∀ i j, j < m → MvPowerSeries.coeff (ee i j) F = 0) →
    ∀ i j, j < 2 * m → MvPowerSeries.coeff (ee i j) (mvExp F) =
      MvPowerSeries.coeff (ee i j) (1 : MvPowerSeries (Fin 2) C) + MvPowerSeries.coeff (ee i j) F

def GaugeLeadingTermLinear : Prop :=
  ∀ (C : Type) [Field C] (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ),
    (∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 1) → MvPowerSeries.coeff e X.h = 0) →
    ∀ x c : κ → PowerSeries C, (∀ i, PowerSeries.constantCoeff (x i) = 0) → ∀ m : ℕ, 1 ≤ m →
    (∀ i j, j < m → PowerSeries.coeff j (c i) = 0) →
    (∀ n j, j < m → MvPowerSeries.coeff (ee n j) (HH X x c) = 0) ∧
      ∀ n, MvPowerSeries.coeff (ee n m) (HH X x c) =
        -PowerSeries.coeff n (alongCv x (X.sg fun i => PowerSeries.coeff m (c i)))

def GaugeRescalingSymmetry : Prop :=
  ∀ (C : Type) [Field C] (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ) (x z : κ → PowerSeries C), (∀ i, PowerSeries.constantCoeff (x i) = 0) →
    (∀ i, PowerSeries.constantCoeff (z i) = 0) → ∀ c : C,
    HH X (rc c x) z = rs 0 c (HH X x z) ∧ HH X x (rc c z) = rs 1 c (HH X x z)

def IntegralUnitFamilies : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ), Basic X V → BiInt X V → ∀ ζ : C, ζ ^ V.l = 1 → ∀ (n : ℕ), 0 < n →
    ∀ γ δ c : κ → PowerSeries C, IsCv V γ → IsCv V δ → IsCv V c → NormRel X V.l n ζ γ δ →
    IntS V (mvExp (∑ k ∈ Finset.range V.l, HH X (rc (ζ ^ k) γ) c - HH X (pw n δ) c)) ∧
      IntS V (mvExp (∑ k ∈ Finset.range V.l, HH X c (rc (ζ ^ k) γ) - HH X c (pw n δ)))

def GenericPointUnitCongruence : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ), Basic X V → BiInt X V → ∀ ζ : C, ζ ^ V.l = 1 → ∀ (n : ℕ), 0 < n →
    ∀ z ε δ : κ → PowerSeries C, IsCv V z → IsCv V ε → IsCv V δ → NormRel X V.l n ζ z ε →
    (∀ i, V.MM (PowerSeries.coeff 1 (δ i))) → ∀ N : ℕ, 0 < N → ∀ i j, i ≤ N →
    V.MM (MvPowerSeries.coeff (ee i j)
      (mvExp (∑ k ∈ Finset.range V.l, HH X (pw N δ) (rc (ζ ^ k) z) - HH X (pw N δ) (pw n ε)) - 1))

end Formalism.L2.FormalSeriesBounds
