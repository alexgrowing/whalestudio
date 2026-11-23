import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.Transfer

noncomputable section

open Finset

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

variable {Y : Type}

def fc {n : ℕ} (i : ℕ) (l : Fin n) : Fin (n + 1) :=
  ⟨if (l : ℕ) < i then (l : ℕ) else (l : ℕ) + 1, by split_ifs <;> omega⟩

theorem fc_val {n : ℕ} (i : ℕ) (l : Fin n) :
    ((fc i l : Fin (n + 1)) : ℕ) = if (l : ℕ) < i then (l : ℕ) else (l : ℕ) + 1 :=
  rfl

theorem succAbove_eq_fc {n : ℕ} (i : Fin (n + 1)) (l : Fin n) : i.succAbove l = fc i l := by
  apply Fin.ext
  rw [fc_val]
  rcases Nat.lt_or_ge (l : ℕ) (i : ℕ) with h | h
  · rw [if_pos h, Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]
    rfl
  · rw [if_neg (by omega), Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using h)]
    rfl

theorem dc_eq {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) (y : Fin (m + 2) → Y) :
    dc F y = ∑ i : Fin (m + 2), (-1 : ℝ) ^ (i : ℕ) * F (fun l => y (fc i l)) := by
  simp only [dc, succAbove_eq_fc]

theorem dc_smul {m : ℕ} (r : ℝ) (F : (Fin (m + 1) → Y) → ℝ) : dc (r • F) = r • dc F := by
  funext y; simp [dc, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring

theorem dc_sub {m : ℕ} (F G : (Fin (m + 1) → Y) → ℝ) : dc (F - G) = dc F - dc G := by
  funext y; simp [dc, mul_sub, Finset.sum_sub_distrib]

private theorem fc_fc_eq_fc_fc_pred_of_lt {n : ℕ} (i j : ℕ) (hji : j < i) (l : Fin n) :
    (fc i (fc j l) : Fin (n + 2)) = fc j (fc (i - 1) l) := by
  apply Fin.ext
  simp only [fc_val]
  split_ifs <;> omega

theorem dc_dc {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) : dc (dc F) = 0 := by
  funext y
  rw [Pi.zero_apply, dc_eq]
  simp only [dc_eq, Finset.mul_sum]
  rw [← Finset.sum_product' (Finset.univ : Finset (Fin (m + 1 + 2)))
    (Finset.univ : Finset (Fin (m + 2)))
    (fun i j => (-1 : ℝ) ^ (i : ℕ) * ((-1 : ℝ) ^ (j : ℕ) * F (fun l => y (fc i (fc j l)))))]
  refine Finset.sum_involution (fun p _ => if h : (p.2 : ℕ) < (p.1 : ℕ) then
      ((⟨p.2, by have := p.1.isLt; have := p.2.isLt; omega⟩ : Fin (m + 1 + 2)),
        (⟨p.1 - 1, by have := p.1.isLt; have := p.2.isLt; omega⟩ : Fin (m + 2)))
    else ((⟨p.2 + 1, by have := p.1.isLt; have := p.2.isLt; omega⟩ : Fin (m + 1 + 2)),
      (⟨p.1, by have := p.1.isLt; have := p.2.isLt; omega⟩ : Fin (m + 2)))) ?_ ?_ ?_ ?_
  · intro p _
    split_ifs with h
    · simp only [Fin.val_mk, fc_fc_eq_fc_fc_pred_of_lt _ _ h]
      obtain ⟨t, ht⟩ : ∃ t, (p.1 : ℕ) = t + 1 := ⟨p.1 - 1, by omega⟩
      simp only [ht, Nat.add_sub_cancel, pow_succ]
      ring
    · simp only [Fin.val_mk, fc_fc_eq_fc_fc_pred_of_lt ((p.2 : ℕ) + 1) p.1 (by omega), Nat.add_sub_cancel,
        pow_succ]
      ring
  · intro p _ _
    split_ifs with h
    · intro he
      rw [Prod.ext_iff, Fin.ext_iff, Fin.ext_iff] at he
      simp only [Fin.val_mk] at he
      omega
    · intro he
      rw [Prod.ext_iff, Fin.ext_iff, Fin.ext_iff] at he
      simp only [Fin.val_mk] at he
      omega
  · intro p _
    simp
  · intro p _
    obtain ⟨i, j⟩ := p
    by_cases h : (j : ℕ) < (i : ℕ)
    · have h' : ¬ ((i : ℕ) - 1 < (j : ℕ)) := by omega
      simp only [h, h', dif_pos, dif_neg, not_false_eq_true, Prod.mk.injEq, Fin.ext_iff, Fin.val_mk]
      exact ⟨by omega, trivial⟩
    · have h' : (i : ℕ) < (j : ℕ) + 1 := by omega
      simp only [h, h', dif_pos, dif_neg, not_false_eq_true, Prod.mk.injEq, Fin.ext_iff, Fin.val_mk]
      exact ⟨trivial, by omega⟩

end PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

end
