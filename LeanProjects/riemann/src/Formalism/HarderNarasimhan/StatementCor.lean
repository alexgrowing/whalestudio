import Mathlib
import Formalism.HarderNarasimhan.Statement

open Module Submodule

noncomputable section

namespace Formalism.HN

def HNCor : Prop :=
  ∀ (R V E : Type*) [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E) (L : Submodule R V),
    IsLat ρ L →
    Antitone (hnStep ρ L) ∧
    (L ≠ ⊥ → ∀ θ : ℝ, hnStep ρ L θ = L ↔ θ ≤ muMin ρ L) ∧
    (∀ θ : ℝ, muMax ρ L < θ → hnStep ρ L θ = ⊥) ∧
    (∀ t : ℝ, (Finset.univ.filter (fun j => slopeList ρ L j < t)).card =
      rk ρ L - rk ρ (hnStep ρ L t)) ∧
    (∀ N : Submodule R V, N ≤ L → N ≠ ⊥ → muMax ρ N ≤ muMax ρ L) ∧
    (∀ (N : Submodule R V) (θ : ℝ), N ≤ L → N ≠ ⊥ → θ ≤ muMin ρ N →
      rk ρ N ≤ (Finset.univ.filter (fun j => θ ≤ slopeList ρ L j)).card)

def ImageStep : Prop :=
  ∀ (R ι W F : Type*) [Ring R] [AddCommGroup W] [Module R W] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (V E : ι → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)]
    (ρ : ∀ i, V i →+ E i) (ρ' : W →+ F) (L : ∀ i, Submodule R (V i)) (M : Submodule R W)
    (s : Finset ι) (φ : ∀ i, L i →ₗ[R] M) (C : ι → ℝ) (θ : ℝ),
    (∀ i ∈ s, IsLat (ρ i) (L i)) → IsLat ρ' M →
    (∀ i ∈ s, 0 < C i ∧ (∀ x : L i, ‖ρ' (φ i x : W)‖ ≤ C i * ‖ρ i (x : V i)‖) ∧
      (L i ≠ ⊥ → θ ≤ muMin (ρ i) (L i) - Real.log (C i))) →
    (⨆ i ∈ s, (LinearMap.range (φ i)).map M.subtype) ≤ hnStep ρ' M θ

end Formalism.HN
