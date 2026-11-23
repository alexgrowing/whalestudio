import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellLocSys
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def RowLocCover.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ)
    (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ (γ : K → ℤ)
      (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)),
      ∃ (m : ℕ) (f u : Fin m → Ω),
        (∀ l, f l ∈ Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J) ∧
        (∀ l, u l ∈ Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J) ∧
        ∑ l, u l * f l = 1 ∧
        ∀ l, ∃ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) ∧
          (∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → ¬ CellMeets y I →
            cellLocSys (fun I => cellSec F y γ (baseCell k₀ e J.1 I)) (f l) I = ⊥) ∧
          (∀ I I' : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → (∀ k, I k ⊆ I' k) → CellMeets y I' →
            cellLocSys (fun I => cellSec F y γ (baseCell k₀ e J.1 I)) (f l) I ≤
              cellLocSys (fun I => cellSec F y γ (baseCell k₀ e J.1 I)) (f l) I') ∧
          (∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → ∀ k,
            cellLocSys (fun I => cellSec F y γ (baseCell k₀ e J.1 I)) (f l)
                (Function.update I k (insert (c k) (I k))) =
              cellLocSys (fun I => cellSec F y γ (baseCell k₀ e J.1 I)) (f l) I)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
