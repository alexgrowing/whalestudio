import Mathlib

namespace GlobalTheory.ThK.RankRed

def HasConstTerm {Z : Type} [AddCommGroup Z] [TopologicalSpace Z] (Λ : Set Z) (f : Z → ℂ) (c : ℂ) : Prop :=
  ∃ (ι : Type) (a : ι → ℂ) (χ : ι → AddChar Z ℂ), Countable ι ∧ Summable (fun k => ‖a k‖) ∧
    (∀ k, Continuous (χ k) ∧ (∀ z, ‖χ k z‖ = 1) ∧ (∀ z ∈ Λ, χ k z = 1) ∧ χ k ≠ 1) ∧
    ∀ z, f z = c + ∑' k, a k * χ k z

end GlobalTheory.ThK.RankRed
