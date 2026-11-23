import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PlaceB

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

variable {p n' k1 t m c r : ℕ} {TT : Finset (Fin n')} {a b : Fin n' → ℤ} {lam0 : Fin n' → Fin (k1 + 1) → ℤ}
  {w : ℕ → Fin n' → ℤ}

theorem w_one_le (h : Std p n' k1 t m c r TT a b lam0 w) (s : Fin n') :
    ∀ j, 1 ≤ j → j ≤ m → w 1 s ≤ w j s := by
  intro j hj hm
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with hj0 | hj'
    · subst hj0
      exact le_rfl
    · exact (ih hj' (by omega)).trans (h.w_mono s j hj' (by omega))

theorem lamI_ge_last (h : Std p n' k1 t m c r TT a b lam0 w) (s : Fin n') (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ k1 + 1) :
    lam0 s (Fin.last k1) ≤ lamI lam0 s i := by
  unfold lamI
  rw [dif_pos ⟨h1, h2⟩]
  exact h.dom s (Fin.le_last _)

theorem lamI_add_w_nonneg (h : Std p n' k1 t m c r TT a b lam0 w) (s : Fin n') (i j : ℕ) (h1 : 1 ≤ i)
    (h2 : i ≤ k1 + 1) (hj : 1 ≤ j) (hm : j ≤ m) : 0 ≤ lamI lam0 s i + w j s := by
  have h3 := lamI_ge_last h s i h1 h2
  have h4 := w_one_le h s j hj hm
  have h5 := (h.w_low s).2
  linarith

theorem al_nonneg (h : Std p n' k1 t m c r TT a b lam0 w) (s : Fin n') : 0 ≤ al TT lam0 s := by
  have hk : 2 ≤ k1 + 1 := by have := h.two_r; have := h.r_pos; omega
  unfold al
  split_ifs
  · unfold lamI
    rw [dif_pos (show 1 ≤ 1 ∧ 1 ≤ k1 + 1 by omega), dif_pos (show 1 ≤ 2 ∧ 2 ≤ k1 + 1 by omega)]
    exact sub_nonneg.mpr (h.dom s (Fin.mk_le_mk.mpr (by omega)))
  · exact le_rfl

theorem cap_nonneg (h : Std p n' k1 t m c r TT a b lam0 w) (s : Fin n') (j : ℕ) (hj : 1 ≤ j) (hm : j ≤ m) :
    0 ≤ cap t TT lam0 w j s := by
  have hk : 2 ≤ k1 + 1 := by have := h.two_r; have := h.r_pos; omega
  unfold cap nu
  split_ifs <;> first
    | omega
    | exact lamI_add_w_nonneg h s _ j (by omega) (by omega) hj hm

theorem gam_nonneg (h : Std p n' k1 t m c r TT a b lam0 w) : 0 ≤ gam p := by
  unfold gam
  have h5 : (5 : ℝ) ≤ p := by exact_mod_cast h.five_le
  apply div_nonneg
  · positivity
  · nlinarith

theorem Pr_nonneg (h : Std p n' k1 t m c r TT a b lam0 w) (j : ℕ) (hj : 1 ≤ j) (hm : j ≤ m) :
    0 ≤ Pr t r lam0 w j := by
  unfold Pr
  have hk := h.two_r
  have hr := h.r_pos
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro s _
    have hcard : (Icc (k1 + 2 - r) (k1 + 1)).card = r := by
      rw [Nat.card_Icc]
      omega
    have key : ∀ a ∈ Icc (k1 + 2 - r) (k1 + 1), (0 : ℝ) ≤ (w j s : ℝ) + (lamI lam0 s a : ℝ) := by
      intro a ha
      rw [Finset.mem_Icc] at ha
      have h0 := lamI_add_w_nonneg h s a j (by omega) ha.2 hj hm
      have h0' : (0 : ℤ) ≤ w j s + lamI lam0 s a := by linarith
      exact_mod_cast h0'
    have hsum := Finset.sum_nonneg key
    rw [Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul] at hsum
    linarith
  · positivity

theorem gA_ge (p t : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j : ℕ) :
    -de p t TT lam0 w j ≤ gA p t TT lam0 w j := by
  unfold gA
  have key : ∀ X Y : ℝ, 0 ≤ X → -Y ≤ X - Y := fun X Y hX => by linarith
  apply key
  apply Finset.sum_nonneg
  intro s _
  apply tsum_nonneg
  intro e
  split_ifs
  · exact le_rfl
  · exact le_max_right _ _

theorem gB_le (h : Std p n' k1 t m c r TT a b lam0 w) (j : ℕ) (hj : 1 ≤ j) (hm : j ≤ m) :
    gB p t TT lam0 w j ≤ gam p * ∑ s ∈ TT, (al TT lam0 s : ℝ) - de p t TT lam0 w j := by
  unfold gB
  have key : ∀ A X Y : ℝ, 0 ≤ X → A - X - Y ≤ A - Y := fun A X Y hX => by linarith
  apply key
  apply Finset.sum_nonneg
  intro s _
  apply tsum_nonneg
  intro e
  apply le_min
  · apply div_nonneg
    · exact_mod_cast al_nonneg h s
    · positivity
  · exact_mod_cast cap_nonneg h _ j hj hm

theorem relative_presentation_of_d7 (D : Formalism.BasicNotions.D7) : RelativePresentationLiterature D := by
  intro p n' k1 t m c r TT a b lam0 w h
  unfold Sv
  have hA : 0 ≤ gam p * ∑ s ∈ TT, (al TT lam0 s : ℝ) :=
    mul_nonneg (gam_nonneg h) (Finset.sum_nonneg fun s _ => by exact_mod_cast al_nonneg h s)
  calc ∑ j ∈ Icc 1 m, max (gB p t TT lam0 w j - Pr t r lam0 w j - gA p t TT lam0 w j) 0
      ≤ ∑ j ∈ Icc 1 m, gam p * ∑ s ∈ TT, (al TT lam0 s : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [Finset.mem_Icc] at hj
        have e1 := gB_le h j hj.1 hj.2
        have e2 := Pr_nonneg h j hj.1 hj.2
        have e3 := gA_ge p t TT lam0 w j
        exact max_le (by linarith) hA
    _ = (m : ℝ) * gam p * ∑ s ∈ TT, (al TT lam0 s : ℝ) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        ring

end Formalism.MainNotions.FormalGroupSystem.Pf
