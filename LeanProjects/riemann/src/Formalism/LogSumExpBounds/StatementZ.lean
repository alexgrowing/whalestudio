import Mathlib

namespace Formalism.NuclearRankWeightBounds.Z

open Finset

def LatSum : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (f : ℕ) (La : AddSubgroup (Fin f → ℂ)) (x : Fin f → ℝ) (K : ℕ) (S : Finset (Fin f → ℂ)),
      (∀ o ∈ La, o ≠ 0 → 1 ≤ ∏ v, ‖o v‖) → (∀ v, 0 < x v) → ∏ v, x v < 1 → 3 ≤ K →
      (∀ o ∈ S, o ∈ La ∧ o ≠ 0) →
      ∑ o ∈ S, ∏ v, min 1 ((x v / ‖o v‖) ^ K)
        ≤ C ^ f * (∏ v, x v) ^ ((K : ℝ) - 5 / 2)

def ZLift : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (f : ℕ) (La : AddSubgroup (Fin f → ℂ)) (x : Fin f → ℝ) (K : ℕ)
      (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (Z : Finset (Fin f → ℂ)) (U : (Fin f → ℂ) → H) (B : ℝ),
      (∀ o ∈ La, o ≠ 0 → 1 ≤ ∏ v, ‖o v‖) → (∀ v, 0 < x v) → ∏ v, x v < 1 → 3 ≤ K →
      (∀ z ∈ Z, ∀ v, z v ≠ 0) →
      (∀ z ∈ Z, ∀ z' ∈ Z, (fun v => (z v)⁻¹ - (z' v)⁻¹) ∉ La → inner ℂ (U z) (U z') = 0) →
      (∀ A : Finset (Fin f),
        ∑ z ∈ Z, (∏ v ∈ A, (2 / (x v * ‖z v‖)) ^ (2 * K)) * ‖U z‖ ^ 2 ≤ B) →
      ∑ z ∈ Z, ∑ z' ∈ Z.erase z, ‖inner ℂ (U z) (U z')‖
        ≤ C ^ f * (∏ v, x v) ^ ((K : ℝ) - 5 / 2) * B

end Formalism.NuclearRankWeightBounds.Z
