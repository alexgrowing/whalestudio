import Mathlib

universe u_1 u_2

namespace GlobalTheory.BandLemmaFirst

theorem main :
    (let d1 : {k : Type u_1} → [Field k] → {ι : Type u_2} → (ι → ℕ) → ℕ → Matrix ι ι k → Prop :=
      @(fun {k : Type u_1} [Field k] {ι : Type u_2} (ℓ : ι → ℕ) (j : ℕ) (X : Matrix ι ι k) ↦
        ∀ (r s : ι), ℓ s < ℓ r + j → X r s = (0 : k));
    ∀ {k : Type u_1} [inst : Field k] {ι : Type u_2} [Fintype ι] [DecidableEq ι] {ℓ : ι → ℕ} {j : ℕ}
      {X Y : Matrix ι ι k}, d1 ℓ j X → d1 ℓ j Y → d1 ℓ j (X + Y)) := by
  intro d1 k _ ι _ _ ℓ j X Y hX hY r s h
  show (X + Y) r s = 0
  rw [Matrix.add_apply, hX r s h, hY r s h, add_zero]

end GlobalTheory.BandLemmaFirst
