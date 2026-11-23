import Mathlib

noncomputable section

namespace PositivityTheory.Rg.BcB.F.FrE

abbrev Tup {ι : Type} (H : ι → Type) [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)] [∀ s, CompleteSpace (H s)]
    (J : Type) : Type := (∀ s, H s →L[ℂ] H s) × (J → ℂ) × ℂ

def TBound {ι : Type} [Fintype ι] {H : ι → Type} [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)]
    [∀ s, CompleteSpace (H s)] {J Γ : Type} [Fintype J] (gen : Γ → Tup H J) (V : ∀ s, Submodule ℂ (H s))
    (X : ∀ s, H s →L[ℂ] H s) : Prop :=
  ∃ ρ : ℝ, ∀ a ∈ StarAlgebra.adjoin ℂ (Set.range gen), ∀ ε : ℝ, 0 < ε → ∃ (C : ℝ) (N : ℕ), ∀ᶠ k : ℕ in Filter.atTop,
    ‖a.2.2‖ ^ k ≤ C * (1 + k) ^ N * (∑ s, ‖((X s * a.1 s) ^ k) ∘L (V s).subtypeL‖ + ∑ j, (ρ * ‖a.2.1 j‖) ^ k) + C * ε ^ k

def TChar {ι : Type} {H : ι → Type} [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)]
    [∀ s, CompleteSpace (H s)] {J Γ : Type} (gen : Γ → Tup H J) (V : ∀ s, Submodule ℂ (H s)) (X : ∀ s, H s →L[ℂ] H s) (s : ι) :
    Prop :=
  ∃ χ : StarAlgebra.adjoin ℂ (Set.range (fun x => (gen x).1 s) ∪ {star (X s) * X s}) →⋆ₐ[ℂ] ℂ,
    (∀ y, ‖χ y‖ ≤ ‖(y : H s →L[ℂ] H s) ∘L (V s).subtypeL‖) ∧
    (∀ x, χ ⟨(gen x).1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨x, rfl⟩)⟩ = (gen x).2.2) ∧
    χ ⟨star (X s) * X s, StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)⟩ ≠ 0

def AbsD : Prop := ∀ (ι : Type) [Fintype ι] (H : ι → Type) [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)]
  [∀ s, CompleteSpace (H s)] (J Γ : Type) [Fintype J] (gen : Γ → Tup H J) (V : ∀ s, Submodule ℂ (H s)) (X : ∀ s, H s →L[ℂ] H s),
  (∀ s, IsClosed (V s : Set (H s))) → (∀ x y s, Commute ((gen x).1 s) ((gen y).1 s) ∧ Commute ((gen x).1 s) (star ((gen y).1 s))) →
  (∀ x s, Commute (X s) ((gen x).1 s) ∧ Commute (X s) (star ((gen x).1 s))) →
  (∀ s, ∀ v ∈ V s, (∀ x, (gen x).1 s v ∈ V s ∧ star ((gen x).1 s) v ∈ V s) ∧ X s v ∈ V s ∧ star (X s) v ∈ V s) →
  TBound gen V X → (∃ j, ∀ x, (gen x).2.1 j = (gen x).2.2) ∨ ∃ s, TChar gen V X s

end PositivityTheory.Rg.BcB.F.FrE

end
