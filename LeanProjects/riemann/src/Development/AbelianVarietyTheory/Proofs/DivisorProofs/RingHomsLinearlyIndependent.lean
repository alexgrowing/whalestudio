import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem ringHom_independent_via_algebraMap :
    ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ],
      Function.Injective (algebraMap O C) → ∀ (S : Finset (Λ →+* O)) (c : (Λ →+* O) → C),
        (∀ a : Λ, ∑ σ ∈ S, c σ * algebraMap O C (σ a) = 0) → ∀ σ ∈ S, c σ = 0 := by
  intro C _ O _ _ Λ _ hinj S c hsum
  classical
  let φ : (Λ →+* O) → (Λ →* C) := fun σ => ((algebraMap O C).comp σ).toMonoidHom
  have hφ : Function.Injective φ := by
    intro σ τ h
    ext a
    apply hinj
    have := congrArg (fun f : Λ →* C => f a) h
    simpa [φ] using this
  have hli := (linearIndependent_monoidHom Λ C).comp φ hφ
  rw [linearIndependent_iff'] at hli
  intro σ hσ
  apply hli S c _ σ hσ
  funext a
  simpa [φ, Finset.sum_apply] using hsum a

end GlobalTheory
