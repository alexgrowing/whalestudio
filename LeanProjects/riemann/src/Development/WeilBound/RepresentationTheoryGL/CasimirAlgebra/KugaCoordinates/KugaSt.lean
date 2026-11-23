import Mathlib

noncomputable section

namespace PositivityTheory.Rg.Cz

def KugaAbs : Prop :=
  ∀ (P : Type) [AddCommGroup P] [Module ℝ P] (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
    (β γ : Type) [Fintype β] [Fintype γ] (b : β → P) (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ)
    (a r : P →ₗ[ℝ] Module.End ℂ M) (a' r' : γ → Module.End ℂ M) (D : γ → P →ₗ[ℝ] P) (c : β → β → γ → ℝ),
    Submodule.span ℝ (Set.range b) = ⊤ → (∀ x y, B y x = starRingEnd ℂ (B x y)) → (∀ x, x ≠ 0 → 0 < (B x x).re) →
    (∀ X x y, B (a X x) y = -B x (a X y)) → (∀ X x y, B (r X x) y = B x (r X y)) →
    (∀ X Y, Commute (a X) (r Y)) → (∀ k, Commute (a' k) (r' k)) →
    (∀ i j, a (b i) * a (b j) - a (b j) * a (b i) = ∑ k, (c i j k : ℂ) • a' k) →
    (∀ i j, r (b i) * r (b j) - r (b j) * r (b i) = ∑ k, (c i j k : ℂ) • r' k) →
    (∀ i j k, c j i k = -c i j k) → (∀ k j, D k (b j) = ∑ i, c i j k • b i) →
    (∀ x, (B (((∑ i, r (b i) * r (b i) - ∑ k, r' k * r' k) - (∑ i, a (b i) * a (b i) - ∑ k, a' k * a' k) :
      Module.End ℂ M) x) x).re ≤ 0) →
    ∀ (q : ℕ) (ω : P [⋀^Fin q]→ₗ[ℝ] M),
      (∀ k (Y : Fin q → P), (a' k + r' k) (ω Y) = ∑ s, ω (Function.update Y s (D k (Y s)))) →
      ∀ X : Fin (q + 1) → P, ∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • (a (X i) + r (X i)) (ω (i.removeNth X)) = 0

end PositivityTheory.Rg.Cz

end
