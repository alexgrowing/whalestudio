import Mathlib
import Formalism.GaussValuationBounds.Statement
import Formalism.GaussValuationBounds.GaussUnit
import Formalism.FrobeniusContraction.Statement

noncomputable section

open scoped ENNReal

namespace Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds

def sigUp (ℓ E M j : ℕ) : ℕ :=
  ⌈((E : ℝ) + (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) * (ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2⌉₊ + 1

def TruncUp : Prop :=
  ∀ (A : Type) [CommRing A] (ℓ : ℕ) [Fact ℓ.Prime], 3 ≤ ℓ →
    ∀ (X u : A) (p : ℕ → A) (y M j : ℕ), 1 ≤ j →
      p (j - 1) ∈ Ideal.span {(ℓ : A), X ^ (ℓ ^ (j - 1))} →
      ∀ r : ℕ,
        (ℓ : A) ^ sigUp ℓ y M j * (u * X * ∏ s ∈ Finset.range j, p s ^ (ℓ - 1)) ^ r ∈
          Ideal.span {(ℓ : A) ^ ⌈(r : ℝ) * ℓ / ((ℓ : ℝ) - 1)⌉₊,
            X ^ M * ∏ s ∈ Finset.range j, p s ^ y}

def SigBoundUp : Prop :=
  ∀ (ℓ : ℕ), 3 ≤ ℓ → ∀ (g h j : ℕ), 1 ≤ j →
    (sigUp ℓ (3 * g) ((h + 2 * g) / (ℓ - 1) + 1) j : ℝ) ≤
      3 / 2 * ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) ^ (j + 1) + 9 / 4 * g + 11 / 4

def ExpUp : Prop :=
  ∀ (ℓ : ℕ), 3 ≤ ℓ → ∀ (g h j ell : ℕ), 1 ≤ j → ∀ (r κ R K : ℝ), 0 ≤ r → r ≤ R → κ ≤ K →
    let σ : ℝ := sigUp ℓ (3 * g) ((h + 2 * g) / (ℓ - 1) + 1) j
    2 * r + 4 * σ + 2 * (2 * σ + r + 2 * g * ell) + 2 * κ ≤
      4 * R + 8 * (3 / 2 * ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) ^ (j + 1) + 9 / 4 * g + 11 / 4) +
        4 * g * ell + 2 * K

def RationalTailBound : Prop :=
  ∀ (ℓ : ℝ), 11 ≤ ℓ → ∀ j : ℕ, 1 ≤ j →
    2 * ℓ ^ 2 / ℓ ^ j / (ℓ - 1) ^ 3 + 2 * ℓ / ((ℓ - 2) * (ℓ - 1) ^ (j + 1)) ≤ 0.06

def EisE {O : Type} [CommRing O] (ϖ : O) (e : ℕ) (E : Polynomial O) (N : ℕ) : Prop :=
  E.Monic ∧ E.natDegree = N ∧ (∀ i < N, E.coeff i ∈ Ideal.span {ϖ ^ e}) ∧ E.coeff 0 ∉ Ideal.span {ϖ ^ (e + 1)}

def GaussEisRam : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (e : ℕ), 1 ≤ e → ∀ (x : ℝ), 0 ≤ x → ∀ (E : Polynomial O) (N : ℕ), 1 ≤ N → EisE ϖ e E N →
      Formalism.NOK.gaussV x (E : PowerSeries O) = ENNReal.ofReal (min (e : ℝ) (x * N))

def LemmaCValRam : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (e : ℕ), 1 ≤ e → ∀ (ℓ : ℕ), 2 ≤ ℓ →
    ∀ (E : ℕ → Polynomial O) (u : ℕ → PowerSeries O),
      (∀ s, EisE ϖ e (E s) (ℓ ^ s)) → (∀ s, IsUnit (u s)) →
      ∀ (ell g a b₀ b₁ s₀ s₁ k : ℕ), s₀ < s₁ →
        2 * ((a : ℝ) + 2 * e * g * ell) < e * b₁ → 2 * b₀ ≤ ℓ * b₁ →
        PowerSeries.C (ϖ ^ a) *
            (∏ s ∈ Finset.range ell, (u s * (E s : PowerSeries O)) ^ g) ^ 2 *
            (u s₀ * (E s₀ : PowerSeries O)) ^ b₀ ∈
          Ideal.span {PowerSeries.C (ϖ ^ k), (u s₁ * (E s₁ : PowerSeries O)) ^ b₁} →
        (k : ℝ) ≤ ((a : ℝ) + 2 * e * g * ell) * b₁ / (b₁ - b₀ / ℓ) ∧
          (k : ℝ) ≤ 2 * ((a : ℝ) + 2 * e * g * ell)

end Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds
