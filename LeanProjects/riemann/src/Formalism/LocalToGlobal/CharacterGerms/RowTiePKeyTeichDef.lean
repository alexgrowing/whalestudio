import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyDef

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKey

def TeichSt : Prop :=
  ∀ (C : Type) [Field C] (V : VF C),
    (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) →
    ∀ (n d : ℕ), d ≠ 0 → ∀ (A : Set (Matrix (Fin n) (Fin n) C)),
      (∀ a ∈ A, ∀ b ∈ A, a + b ∈ A) → (∀ a ∈ A, -a ∈ A) → (∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, ∀ i j, V.Ge 0 (a i j)) →
      (∀ (s : ℕ → Matrix (Fin n) (Fin n) C) (b : Matrix (Fin n) (Fin n) C), (∀ k, s k ∈ A) →
        (∀ i j, RowTiePE0.Tends V (fun k => s k i j) (b i j)) → b ∈ A) →
      (∀ a ∈ A, ((V.l : C)⁻¹) • (a ^ V.l ^ d - a) ∈ A) →
      ∀ b ∈ A, ∃ τ ∈ A, τ ^ V.l ^ d = τ ∧ ((V.l : C)⁻¹) • (b - τ) ∈ A

end RowTiePKey

end Formalism.L2.FormalSeriesBounds
