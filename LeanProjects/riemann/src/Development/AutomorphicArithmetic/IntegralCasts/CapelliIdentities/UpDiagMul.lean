import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe40.M4 :
    Type → Type :=
    fun (R : Type) ↦ Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) R

noncomputable def UpperTheory.Reformulated.B.Qe40.IsUp :
    {R : Type} → [CommRing R] → UpperTheory.Reformulated.B.Qe40.M4 R → Prop :=
    fun {R : Type} [CommRing R] (X : UpperTheory.Reformulated.B.Qe40.M4 R) ↦ ∀ (i j : Fin (4 : ℕ)), j < i → X i j = (0 : R)

theorem UpperTheory.Reformulated.B.Qe40.up_diag_mul :
    ∀ {R : Type} [inst : CommRing R] {X Y : UpperTheory.Reformulated.B.Qe40.M4 R},
      UpperTheory.Reformulated.B.Qe40.IsUp X → UpperTheory.Reformulated.B.Qe40.IsUp Y → ∀ (i : Fin (4 : ℕ)), (X * Y) i i = X i i * Y i i := by
  intro R _ X Y hX hY i
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hX i k h, zero_mul]
  · rw [hY k i h, mul_zero]
