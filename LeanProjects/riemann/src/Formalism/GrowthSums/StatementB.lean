import Mathlib
import Formalism.SubspaceCounting.GoodOrbitIntervalTileCondition

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.GrowthSums

open Formalism.G0

def SegmentBound : Prop :=
  ∀ (n : ℕ) (T : Finset ℕ) (L₂ K r u M₀ G' N₁ : ℕ) (hr : 1 ≤ r), 1 ≤ u →
    (M₀ + 1) * ((6 * r + 1) * u) ≤ n → (M₀ + 5) * ((6 * r + 1) * u) ≤ G' →
    T ⊆ range n → GoodOrbitIntervalTileCondition n T L₂ K r u M₀ G' N₁ →
    ∀ (s s' : ℕ) (f f' : Fin (3 * r) → ℕ),
      s < n / ((6 * r + 1) * u) → s' < n / ((6 * r + 1) * u) →
      Marked T r u s → Marked T r u s' →
      (∀ j, 0 < j →
        j < (if s < s' then s' - s else s' + n / ((6 * r + 1) * u) - s) →
        ¬ Marked T r u ((s + j) % (n / ((6 * r + 1) * u)))) →
      StrictMono f → T ∩ Ico (s * ((6 * r + 1) * u)) ((s + 1) * ((6 * r + 1) * u)) = univ.image f →
      StrictMono f' → T ∩ Ico (s' * ((6 * r + 1) * u)) ((s' + 1) * ((6 * r + 1) * u)) = univ.image f' →
      let a := f ⟨r, by omega⟩
      let b := f' ⟨2 * r - 1, by omega⟩
      let D := if s < s' then b - a else b + n - a
      D < G' ∧ (a + D) % n = b ∧
        (T ∩ (range (D + 1)).image (fun j => (a + j) % n)).card ≤ N₁

def OldestFar : Prop :=
  ∀ (n : ℕ) (T : Finset ℕ) (L₁ L₂ K r : ℕ), 0 < n → L₁ < n → K ≤ r → L₁ + 1 ≤ L₂ → CondA n T L₂ K →
    ∀ i ∈ T, i < n → (T ∩ (Icc 1 L₁).image (fun d => (i + n * L₁ - d) % n)).card < r

def NextEvenTop : Prop :=
  ∀ (n : ℕ) (T : Finset ℕ) (L₂ K r u M₀ G' N₁ : ℕ), 1 ≤ r → 1 ≤ u →
    (M₀ + 1) * ((6 * r + 1) * u) ≤ n → (M₀ + 5) * ((6 * r + 1) * u) ≤ G' →
    T ⊆ range n → GoodOrbitIntervalTileCondition n T L₂ K r u M₀ G' N₁ →
    ∀ i < n, ∃ D ∈ Icc 1 G', (i + D) % n ∈ T ∧ Even ((i + D) % n)

def TopCount : Prop :=
  ∀ (n : ℕ) (T : Finset ℕ) (L₂ K r u M₀ G' N₁ : ℕ), 1 ≤ r → 1 ≤ u →
    (M₀ + 1) * ((6 * r + 1) * u) ≤ n → (M₀ + 5) * ((6 * r + 1) * u) ≤ G' →
    T ⊆ range n → GoodOrbitIntervalTileCondition n T L₂ K r u M₀ G' N₁ →
    n ≤ T.card * G' ∧ T.card * G' ≤ N₁ * (n + G')

end Formalism.GrowthSums
