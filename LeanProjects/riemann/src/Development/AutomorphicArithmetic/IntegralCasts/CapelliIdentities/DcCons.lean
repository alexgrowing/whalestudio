import Mathlib

noncomputable def UpperTheory.Reformulated.B.Qj27.dc :
    {Y : Type} → {m : ℕ} → ((Fin (m + (1 : ℕ)) → Y) → ℝ) → (Fin (m + (2 : ℕ)) → Y) → ℝ :=
    fun {Y : Type} {m : ℕ} (F : (Fin (m + (1 : ℕ)) → Y) → ℝ) (y : Fin (m + (2 : ℕ)) → Y) ↦
      ∑ i : Fin (m + (2 : ℕ)), (-1 : ℝ) ^ (↑i : ℕ) * F fun (j : Fin (m + (1 : ℕ))) ↦ y (i.succAbove j)

theorem UpperTheory.Reformulated.B.Qj27.dc_cons :
    ∀ {Y : Type} {m : ℕ} (F : (Fin (m + (2 : ℕ)) → Y) → ℝ) (a : Y) (w : Fin (m + (2 : ℕ)) → Y),
      UpperTheory.Reformulated.B.Qj27.dc F (Fin.cons a w) =
        F w - UpperTheory.Reformulated.B.Qj27.dc (fun (w' : Fin (m + (1 : ℕ)) → Y) ↦ F (Fin.cons a w')) w := by
  intro Y m F a w
  have h : ∀ i : Fin (m + 2),
      (fun j : Fin (m + 2) ↦ (Fin.cons a w : Fin (m + 3) → Y) (i.succ.succAbove j)) =
        (Fin.cons a (fun j : Fin (m + 1) ↦ w (i.succAbove j)) : Fin (m + 2) → Y) := by
    intro i
    funext j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · simp
    · simp
  unfold UpperTheory.Reformulated.B.Qj27.dc
  rw [Fin.sum_univ_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [h i, Fin.val_succ, pow_succ]
    ring
