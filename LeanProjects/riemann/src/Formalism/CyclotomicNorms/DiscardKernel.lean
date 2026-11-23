import Mathlib

open Finset

noncomputable section

namespace Formalism.CyclotomicNorms

open scoped ComplexOrder

def SubstitutionAdaptive : Prop :=
  ∀ (k : Type) [CommRing k] (ℓ r s : ℕ) (F : Fin s → MvPowerSeries (Fin r) k) (B : List ℕ → ℕ),
    2 ≤ ℓ → (∀ i, F i ≠ 0) →
    ∃ e : Fin r → ℕ, StrictMono e ∧
      (∀ j : Fin r, B (List.ofFn fun i : Fin (j : ℕ) => e (Fin.castLE (Nat.le_of_lt j.isLt) i)) ≤ e j) ∧
      ∀ i, (MvPowerSeries.subst (fun j => (PowerSeries.X : PowerSeries k) ^ (ℓ ^ e j)) (F i) :
        PowerSeries k) ≠ 0

def LowPowerSeries : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (n m₀ : ℕ)
    (D g : PowerSeries O),
    Irreducible ϖ →
    (PowerSeries.map (IsLocalRing.residue O) D).order ≤ (m₀ : ℕ∞) →
    PowerSeries.constantCoeff g ∉ Ideal.span {ϖ ^ n} →
    D * g ∉ Ideal.span {PowerSeries.C (ϖ ^ n), (PowerSeries.X : PowerSeries O) ^ (n * m₀ + 1)}

def PermFixedSet : Prop :=
  ∀ N a : ℕ, 0 < a → a < N →
    8 * (univ.filter (fun σ : Equiv.Perm (Fin N) =>
      ∃ S : Finset (Fin N), S.card = a ∧ S.map σ.toEmbedding = S)).card ≤ 7 * N.factorial

def DiscardRatio : Prop :=
  ∀ (n : ℕ) (Q Pi : Matrix (Fin n) (Fin n) ℂ) (δ Dstar η s : ℝ),
    Q.PosSemidef → Pi.IsHermitian → Pi * Pi = Pi → 0 ≤ δ → 2 * δ < 1 → 0 < Dstar →
    (Pi.rank : ℝ) ≤ δ * Dstar → 0 ≤ s → (n : ℝ) ≤ (1 + s) * Dstar → 0 ≤ η → η ≤ 1 →
    (Q * Q).trace.re ≤ (1 + η) * (Q.trace.re) ^ 2 / Dstar →
    (((1 - Pi) * Q * (1 - Pi)) * ((1 - Pi) * Q * (1 - Pi))).trace.re *
        ((n : ℝ) - Pi.rank) * (1 - Real.sqrt (2 * δ)) ^ 2 ≤
      (1 + η) * (1 + s) * (((1 - Pi) * Q * (1 - Pi)).trace.re) ^ 2

def DiscardRatioDstar : Prop :=
  ∀ (n : ℕ) (Q Pi : Matrix (Fin n) (Fin n) ℂ) (δ Dstar η : ℝ),
    Q.PosSemidef → Pi.IsHermitian → Pi * Pi = Pi → 0 ≤ δ → 2 * δ < 1 → 0 < Dstar →
    (Pi.rank : ℝ) ≤ δ * Dstar → 0 ≤ η → η ≤ 1 →
    (Q * Q).trace.re ≤ (1 + η) * (Q.trace.re) ^ 2 / Dstar →
    (((1 - Pi) * Q * (1 - Pi)) * ((1 - Pi) * Q * (1 - Pi))).trace.re *
        Dstar * (1 - Real.sqrt (2 * δ)) ^ 2 ≤
      (1 + η) * (((1 - Pi) * Q * (1 - Pi)).trace.re) ^ 2

def DiscardKernel : Prop :=
  ∀ (m n : ℕ) (B : Matrix (Fin m) (Fin n) ℂ) (Pi : Matrix (Fin m) (Fin m) ℂ) (c : ℝ),
    Pi.IsHermitian → Pi * Pi = Pi → 0 ≤ c →
    ((c : ℂ) • (B.conjTranspose * B) - (c : ℂ) • (B.conjTranspose * (1 - Pi) * B)).PosSemidef

end Formalism.CyclotomicNorms
