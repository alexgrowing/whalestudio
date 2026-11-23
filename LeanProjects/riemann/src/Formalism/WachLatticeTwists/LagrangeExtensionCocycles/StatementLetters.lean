import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.Statement

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

structure Letters {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] (G : GBase ℓ A)
    (n : ℕ) (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D] where
  pair : ZMod n → GPair G D
  φA : A →+* A
  q : A
  w : A
  φπ : φA G.X = G.X * q
  hq : q = (ℓ : A) * w + G.X ^ (ℓ - 1)
  φ : ZMod n → D →+ D
  φ_smul : ∀ (i : ZMod n) (a : A) (x : D), φ i (a • x) = φA a • φ i x

def Letters.step {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] {G : GBase ℓ A}
    {n : ℕ} {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    (Λ : Letters G n D) (i : ZMod n) : PhiStep ℓ A D D where
  φA := Λ.φA
  π := G.X
  q := Λ.q
  w := Λ.w
  φπ := Λ.φπ
  hq := Λ.hq
  φ := Λ.φ i
  φ_smul := Λ.φ_smul i
  P := (Λ.pair (i - 1)).N
  P' := (Λ.pair (i - 1)).N'
  R := (Λ.pair i).N
  R' := (Λ.pair i).N'

def StatWPrime : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ∀ (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (G : GBase ℓ A)
    (n : ℕ) [NeZero n] (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
    [IsScalarTower ℤ_[ℓ] A D] (Λ : Letters G n D) (Mi hi s : ZMod n → ℕ) (H : ℕ),
    IsGen ℓ G.u →
    (∀ i, ∀ x ∈ (Λ.pair (i - 1)).N, Λ.q ^ Mi i • Λ.φ i x ∈ (Λ.pair i).N) →
    (∀ i, ∀ r ∈ (Λ.pair i).N',
      Λ.q ^ hi i • r ∈ Submodule.span A (Λ.φ i '' ((Λ.pair (i - 1)).N' : Set D))) →
    (∀ g : A, ∃ e : Fin ℓ → A, g = ∑ k : Fin ℓ, G.X ^ (k : ℕ) * Λ.φA (e k)) →
    (∀ i, ∀ x : Fin ℓ → D, (∀ k, x k ∈ (Λ.pair (i - 1)).N) →
      ∑ k : Fin ℓ, G.X ^ (k : ℕ) • Λ.φ i (x k) = 0 → ∀ k, x k = 0) →
    (∀ i, (Λ.pair i).Kills (G.X ^ H)) →
    (∀ i, (Λ.pair i).Kills (G.X ^ s i) ∧ ∀ t, (Λ.pair i).Kills (G.X ^ t) → s i ≤ t) →
    (∀ i, s (i - 1) ≤ Mi i + hi i + cW ℓ H + 2 + (s i + (ℓ - 2)) / (ℓ - 1)) ∧
    (∀ (i : ZMod n) (m : ℕ), (s i : ℝ) ≤
      (∑ a ∈ Finset.range m, (((Mi (i + ((a + 1 : ℕ) : ZMod n)) + hi (i + ((a + 1 : ℕ) : ZMod n)) : ℕ) : ℝ)
        + cW ℓ H + 3) / ((ℓ : ℝ) - 1) ^ a) + (s (i + (m : ZMod n)) : ℝ) / ((ℓ : ℝ) - 1) ^ m) ∧
    (∀ i, (Λ.pair i).Kills ((ℓ : A) ^ cost ℓ 0 (s i)) ∧
      (cost ℓ 0 (s i) : ℝ) < (s i : ℝ) * ℓ / ((ℓ : ℝ) - 1) ^ 2 + cW ℓ H) ∧
    (∀ (i : ZMod n) (j : ℕ) (Gw : ℝ), 0 ≤ Gw →
      (∀ k : ℕ, 1 ≤ k → k ≤ j → ((Mi (i + (k : ZMod n)) + hi (i + (k : ZMod n)) : ℕ) : ℝ) ≤ 2 * Gw) →
      (s i : ℝ) ≤ (2 * Gw + cW ℓ H + 3) * ((ℓ : ℝ) - 1) / ((ℓ : ℝ) - 2) + (H : ℝ) / ((ℓ : ℝ) - 1) ^ j)

end Formalism.RepresentationBoundsCohomology.N2
