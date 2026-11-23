import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellHOfCellSec
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

section

variable (S : Type) [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra S Ω]

def CellPosExact (y : (Σ k, ι k) → Ω) (G : (∀ k, Finset (ι k)) → Submodule S Ω) : Prop :=
  ∀ q : ℕ, ∀ s ∈ cellCOf S G (q + 1), cellD S y (q + 1) s = 0 →
    ∃ t ∈ cellCOf S G q, cellD S y q t = s

end

def CellContract.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
    (G : (∀ k, Finset (ι k)) → Submodule S Ω) (c : ∀ k, ι k),
    (∀ k, y ⟨k, c k⟩ ≠ 0) →
    (∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → ¬ CellMeets y I → G I = ⊥) →
    (∀ I I' : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → (∀ k, I k ⊆ I' k) → CellMeets y I' → G I ≤ G I') →
    (∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → ∀ k,
      G (Function.update I k (insert (c k) (I k))) = G I) →
    CellPosExact S y G

theorem CellContract.hyps :
    (∀ k, (fun _ : (Σ _ : Unit, Fin 2) => (1 : ℚ)) ⟨k, (fun _ => (0 : Fin 2) : ∀ _ : Unit, Fin 2) k⟩ ≠ 0) ∧
    (∀ I : ∀ _ : Unit, Finset (Fin 2), (∀ k, (I k).Nonempty) →
      ¬ CellMeets (fun _ : (Σ _ : Unit, Fin 2) => (1 : ℚ)) I → (⊤ : Submodule ℚ ℚ) = ⊥) ∧
    (∀ I I' : ∀ _ : Unit, Finset (Fin 2), (∀ k, (I k).Nonempty) → (∀ k, I k ⊆ I' k) →
      CellMeets (fun _ : (Σ _ : Unit, Fin 2) => (1 : ℚ)) I' → (⊤ : Submodule ℚ ℚ) ≤ ⊤) ∧
    (∀ I : ∀ _ : Unit, Finset (Fin 2), (∀ k, (I k).Nonempty) → ∀ _ : Unit,
      (⊤ : Submodule ℚ ℚ) = ⊤) :=
  ⟨fun _ => one_ne_zero, fun _ _ h => absurd (fun _ _ _ => one_ne_zero) h, fun _ _ _ _ _ => le_rfl,
    fun _ _ _ => rfl⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
