import Mathlib

noncomputable section

namespace PositivityTheory.Rg.BcB.F

def PeakTraceBound : Prop := ∀ (A : Type) [CommRing A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  (ι : Type) [Fintype ι] [Nonempty ι] (H : ι → Type) [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)]
  [∀ s, CompleteSpace (H s)] (R : ∀ s, A →⋆ₐ[ℂ] (H s →L[ℂ] H s)) (β : ∀ s, H s →L[ℂ] H s) (m : ℕ)
  (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V) (u : Module.End ℂ V)
  (p : A →⋆ₐ[ℂ] ℂ) (a₀ : A),
  (∀ s g, Commute (β s) (R s g)) → (∀ g, Commute u (ρ g)) → p a₀ ≠ 0 →
  (∀ g ∈ Ideal.span {a₀}, ∃ (C : ℝ) (N j : ℕ), ∀ᶠ k : ℕ in Filter.atTop,
    ‖LinearMap.trace ℂ V ((u * ρ g) ^ k)‖ ≤ C * (1 + k) ^ N *
      Finset.univ.sup' Finset.univ_nonempty (fun s => ‖(β s ^ m * R s g) ^ (k - j)‖)) →
  (∃ v : V, v ≠ 0 ∧ u v = v ∧ ∀ g, ρ g v = p g • v) →
  ∃ (s : ι) (χ : StarAlgebra.adjoin ℂ (Set.range (R s) ∪ {star (β s ^ m) * β s ^ m}) →⋆ₐ[ℂ] ℂ),
    (∀ x, ‖χ x‖ ≤ ‖(x : H s →L[ℂ] H s)‖) ∧
    (∀ g, χ ⟨R s g, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨g, rfl⟩)⟩ = p g) ∧
    χ ⟨star (β s ^ m) * β s ^ m, StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)⟩ ≠ 0

end PositivityTheory.Rg.BcB.F

end
