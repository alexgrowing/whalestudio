import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk42.M4 :
    Type → Type :=
    fun (R : Type) ↦ Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) R

noncomputable def UpperTheory.Reformulated.B.Qk42.FGe :
    {R : Type} → [CommRing R] → (Fin (4 : ℕ) → ℤ) → ℤ → UpperTheory.Reformulated.B.Qk42.M4 R → Prop :=
    fun {R : Type} [CommRing R] (m : Fin (4 : ℕ) → ℤ) (p : ℤ) (X : UpperTheory.Reformulated.B.Qk42.M4 R) ↦
      ∀ (i j : Fin (4 : ℕ)), m i - m j < p → X i j = (0 : R)

theorem UpperTheory.Reformulated.B.Qk42.mul :
    ∀ {R : Type} [inst : CommRing R] {m : Fin (4 : ℕ) → ℤ} {p q : ℤ} {A B : UpperTheory.Reformulated.B.Qk42.M4 R},
      UpperTheory.Reformulated.B.Qk42.FGe m p A → UpperTheory.Reformulated.B.Qk42.FGe m q B → UpperTheory.Reformulated.B.Qk42.FGe m (p + q) (A * B) := by
  intro R _ m p q A B hA hB i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : m i - m k < p
  · rw [hA i k hk, zero_mul]
  · rw [hB k j (by omega), mul_zero]
