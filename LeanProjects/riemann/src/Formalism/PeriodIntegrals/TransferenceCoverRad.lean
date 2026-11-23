import Mathlib

open scoped InnerProductSpace

noncomputable section

namespace PI

def TransferenceCoverDiv : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (M : Submodule ℤ V), DiscreteTopology M → Submodule.span ℝ (M : Set V) = ⊤ →
    ∀ κ : ℝ, 0 < κ → (∀ y : V, (∀ x ∈ M, ∃ z : ℤ, inner ℝ x y = (z : ℝ)) → y ≠ 0 → κ ≤ ‖y‖) →
    ∀ x : V, ∃ y ∈ M, ‖x - y‖ ≤ (Module.finrank ℝ V : ℝ) / (2 * κ)

def covRad {N : ℕ} (L : Set (EuclideanSpace ℝ (Fin N))) : ℝ := ⨆ x, Metric.infDist x L

def dualLat {N : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin N))) : Set (EuclideanSpace ℝ (Fin N)) :=
  {y | ∀ x ∈ L, ∃ z : ℤ, inner ℝ x y = (z : ℝ)}

def firstMin {N : ℕ} (S : Set (EuclideanSpace ℝ (Fin N))) : ℝ :=
  sInf {r | ∃ y ∈ S, y ≠ 0 ∧ r = ‖y‖}

def TransferenceCoverRad : Prop :=
  ∀ (N : ℕ) (L : Submodule ℤ (EuclideanSpace ℝ (Fin N))) [DiscreteTopology L], IsZLattice ℝ L →
    covRad (L : Set (EuclideanSpace ℝ (Fin N))) * firstMin (dualLat L) ≤ (N : ℝ) / 2

end PI
