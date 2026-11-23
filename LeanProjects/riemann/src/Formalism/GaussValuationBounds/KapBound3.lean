import Mathlib
import Formalism.GaussValuationBounds.Statement

noncomputable section

namespace Formalism.NOK

def WPrimeCut : Prop :=
  ∀ (n : ℕ) [NeZero n] (ℓ c G Hm : ℝ) (s H : ZMod n → ℝ) (i : ZMod n) (j : ℕ),
    3 ≤ ℓ → 0 ≤ c → 0 ≤ G → (∀ k, H k ≤ Hm) →
    (∀ k : ℕ, 1 ≤ k → k ≤ j → H (i + k) ≤ 2 * G) →
    (∀ k, s (k - 1) ≤ H k + c + 3 + s k / (ℓ - 1)) →
    s i ≤ (2 * G + c + 3) * (ℓ - 1) / (ℓ - 2) + (Hm + c + 3) * (ℓ - 1) / ((ℓ - 2) * (ℓ - 1) ^ j)

def Trunc : Prop :=
  ∀ (A : Type) [CommRing A] (ℓ : ℕ) [Fact ℓ.Prime], 3 ≤ ℓ →
    ∀ (X u : A) (p : ℕ → A) (y M j : ℕ), 1 ≤ j →
      p (j - 1) ∈ Ideal.span {(ℓ : A), X ^ (ℓ ^ (j - 1))} →
      ∀ r : ℕ,
        (ℓ : A) ^ sigNOK ℓ y M j * (u * X * ∏ s ∈ Finset.range j, p s ^ (ℓ - 1)) ^ r ∈
          Ideal.span {(ℓ : A) ^ ⌈(r : ℝ) * ℓ / ((ℓ : ℝ) - 1)⌉₊,
            X ^ M * ∏ s ∈ Finset.range j, p s ^ y}

def KapBound3 : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ∀ (χ : ℤ_[ℓ]ˣ), PadicInt.valuation ((χ : ℤ_[ℓ]) - 1) = 1 →
    ∀ (ell g h : ℕ) (a : Fin 3 → ℤ) (JJ : Finset ℤ),
      JJ ⊆ Finset.univ.biUnion (fun t => Finset.Ico (a t) (a t + 3 * (g : ℤ))) →
      (∀ i ∈ JJ, |i| ≤ 2 * (h : ℤ)) →
      (Formalism.WindowSums.PP ℓ χ ell JJ).eval 1 ≠ 0 ∧
      (PadicInt.valuation ((Formalism.WindowSums.PP ℓ χ ell JJ).eval 1) : ℝ) ≤
        ell + 9 * g * (1 + ell) + 3 * (3 * g / ((ℓ : ℝ) - 1) + Real.logb ℓ (2 * h))

end Formalism.NOK
