import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.StatementLetters

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

def StatWPrimeExt : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ∀ (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (G : GBase ℓ A)
    (n : ℕ) [NeZero n] (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
    [IsScalarTower ℤ_[ℓ] A D] (Λ : Letters G n D) (s : ZMod n → ℕ) (H : ℕ) (π₀ v : A),
    IsGen ℓ G.u → π₀ = v * G.X ^ (ℓ - 1) →
    (∀ i, (Λ.pair i).Kills (G.X ^ H)) →
    (∀ i, (Λ.pair i).Kills (G.X ^ s i) ∧ ∀ t, (Λ.pair i).Kills (G.X ^ t) → s i ≤ t) →
    (∀ (i : ZMod n) (a j : ℕ), ((s i : ℝ) - (j : ℝ)) * (ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2 + (cW ℓ H : ℝ) ≤ (a : ℝ) →
      (Λ.pair i).Kills ((ℓ : A) ^ a * G.X ^ j)) ∧
    (∀ i, (Λ.pair i).Kills (π₀ ^ ((s i + (ℓ - 2)) / (ℓ - 1)))) ∧
    (∀ (i : ZMod n) (r : ℕ), (Λ.pair i).Kills ((ℓ : A) ^ r) →
      (Λ.pair i).Kills ((π₀ + (ℓ : A)) ^ ((s i + (ℓ - 2)) / (ℓ - 1) + r))) ∧
    (∀ i, (Λ.pair i).Kills ((π₀ + (ℓ : A)) ^ ((s i + (ℓ - 2)) / (ℓ - 1) + cost ℓ 0 (s i)))) ∧
    (∀ i, (((s i + (ℓ - 2)) / (ℓ - 1) : ℕ) : ℝ) ≤ (H : ℝ) / ((ℓ : ℝ) - 1) + 1 ∧
      ∀ r : ℕ, r ≤ cost ℓ 0 (s i) →
        (((s i + (ℓ - 2)) / (ℓ - 1) : ℕ) : ℝ) + (r : ℝ) ≤
          (H : ℝ) * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 + (cW ℓ H : ℝ) + 1) ∧
    (∀ Mi hi : ZMod n → ℕ,
      (∀ i, ∀ x ∈ (Λ.pair (i - 1)).N, Λ.q ^ Mi i • Λ.φ i x ∈ (Λ.pair i).N) →
      (∀ i, ∀ r ∈ (Λ.pair i).N',
        Λ.q ^ hi i • r ∈ Submodule.span A (Λ.φ i '' ((Λ.pair (i - 1)).N' : Set D))) →
      (∀ g : A, ∃ e : Fin ℓ → A, g = ∑ k : Fin ℓ, G.X ^ (k : ℕ) * Λ.φA (e k)) →
      (∀ i, ∀ x : Fin ℓ → D, (∀ k, x k ∈ (Λ.pair (i - 1)).N) →
        ∑ k : Fin ℓ, G.X ^ (k : ℕ) • Λ.φ i (x k) = 0 → ∀ k, x k = 0) →
      (∀ i : ZMod n,
        Summable (fun a : ℕ =>
          ((((Mi (i + ((a + 1 : ℕ) : ZMod n)) + hi (i + ((a + 1 : ℕ) : ZMod n)) : ℕ) : ℝ)
            + (cW ℓ H : ℝ) + 3) / ((ℓ : ℝ) - 1) ^ a)) ∧
        (s i : ℝ) ≤ ∑' a : ℕ,
          ((((Mi (i + ((a + 1 : ℕ) : ZMod n)) + hi (i + ((a + 1 : ℕ) : ZMod n)) : ℕ) : ℝ)
            + (cW ℓ H : ℝ) + 3) / ((ℓ : ℝ) - 1) ^ a)) ∧
      (∀ (i : ZMod n) (j : ℕ) (Gw : ℝ), 0 ≤ Gw →
        (∀ k : ℕ, 1 ≤ k → k ≤ j →
          ((Mi (i + (k : ZMod n)) + hi (i + (k : ZMod n)) : ℕ) : ℝ) ≤ 2 * Gw) →
        (cost ℓ 0 (s i) : ℝ) ≤
          (2 * Gw + (cW ℓ H : ℝ) + 3) * (ℓ : ℝ) / (((ℓ : ℝ) - 1) * ((ℓ : ℝ) - 2))
            + (H : ℝ) * (ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 2) + (cW ℓ H : ℝ)))

end Formalism.RepresentationBoundsCohomology.N2
