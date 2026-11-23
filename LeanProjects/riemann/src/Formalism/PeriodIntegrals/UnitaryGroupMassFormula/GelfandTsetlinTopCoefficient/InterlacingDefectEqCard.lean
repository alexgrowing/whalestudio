import Mathlib
import Formalism.PeriodIntegrals.GTDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinTopCoefficient.CardEraseIccMin

noncomputable section

namespace PI.GTNum

open Formalism.BasicNotions PI Finset

variable {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)

theorem lam_le_last (k : ℕ) (hk : k < N) : lam.w ⟨N - 1, by omega⟩ ≤ lam.w ⟨k, hk⟩ :=
  lam.anti (Fin.mk_le_mk.2 (by omega))

theorem sg_le_first (hn : 0 < n) (j : Fin n) : sg.w j ≤ sg.w ⟨0, hn⟩ :=
  sg.anti (Fin.le_iff_val_le_val.2 (Nat.zero_le _))

theorem term_nonneg (hI : Interlace h lam sg) (i : Fin n) : 0 ≤ sg.w i - lam.w ⟨i.1 + 1, by omega⟩ := by
  have := (hI i).2
  omega

theorem determinantWeight_nonneg (hI : Interlace h lam sg) : 0 ≤ D0 h lam sg :=
  Finset.sum_nonneg (fun i _ => term_nonneg h lam sg hI i)

theorem term_le_D0 (hI : Interlace h lam sg) (i : Fin n) :
    sg.w i - lam.w ⟨i.1 + 1, by omega⟩ ≤ D0 h lam sg :=
  Finset.single_le_sum (f := fun i : Fin n => sg.w i - lam.w ⟨i.1 + 1, by omega⟩)
    (fun j _ => term_nonneg h lam sg hI j) (Finset.mem_univ i)

theorem last_le_sg (hI : Interlace h lam sg) (j : Fin n) : lam.w ⟨N - 1, by omega⟩ ≤ sg.w j :=
  le_trans (lam_le_last h lam (j.1 + 1) (by omega)) (hI j).2

theorem interlacing_defect_le_gap (hI : Interlace h lam sg) (hn : 0 < n) :
    D0 h lam sg ≤ sg.w ⟨0, hn⟩ - lam.w ⟨N - 1, by omega⟩ := by
  let t : ℕ → ℤ := fun k => if hk : k < n then sg.w ⟨k, hk⟩ else lam.w ⟨N - 1, by omega⟩
  let a : ℕ → ℤ := fun k => if hk : k < n then sg.w ⟨k, hk⟩ - lam.w ⟨k + 1, by omega⟩ else 0
  have hD : D0 h lam sg = ∑ k ∈ range n, a k := by
    unfold D0
    rw [← Fin.sum_univ_eq_sum_range a n]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [a, dif_pos i.2]
  have ht0 : t 0 = sg.w ⟨0, hn⟩ := by simp only [t, dif_pos hn]
  have htn : t n = lam.w ⟨N - 1, by omega⟩ := by simp only [t, dif_neg (lt_irrefl n)]
  rw [hD, ← ht0, ← htn]
  refine sum_range_le_tele n a t (fun k hk => ?_)
  simp only [a, t, dif_pos hk]
  by_cases hk1 : k + 1 < n
  · rw [dif_pos hk1]
    have := (hI ⟨k + 1, hk1⟩).1
    have e : lam.w ⟨(⟨k + 1, hk1⟩ : Fin n).1, by omega⟩ = lam.w ⟨k + 1, by omega⟩ := rfl
    omega
  · rw [dif_neg hk1]
    have e : lam.w ⟨k + 1, by omega⟩ = lam.w ⟨N - 1, by omega⟩ := congrArg lam.w (Fin.ext (by simp; omega))
    omega

theorem sg_mem_R (hI : Interlace h lam sg) (i : Fin n) : sg.w i ∈ Rset h lam sg i := by
  unfold Rset
  have h1 := hI i
  have h2 := term_le_D0 h lam sg hI i
  rw [Finset.mem_Icc]
  refine ⟨h1.2, le_min h1.1 (by omega)⟩

theorem lam_succ_le (i : Fin n) : lam.w ⟨i.1 + 1, by omega⟩ ≤ lam.w ⟨i.1, by omega⟩ :=
  lam.anti (Fin.mk_le_mk.2 (by omega))

theorem card_R_erase (hI : Interlace h lam sg) (i : Fin n) :
    ((((Rset h lam sg i).erase (sg.w i)).card : ℕ) : ℤ) =
      min (lam.w ⟨i.1, by omega⟩ - lam.w ⟨i.1 + 1, by omega⟩) (D0 h lam sg) := by
  have hm := sg_mem_R h lam sg hI i
  unfold Rset at hm ⊢
  exact card_erase_Icc_min _ _ _ _ (lam_succ_le h lam i) (determinantWeight_nonneg h lam sg hI) hm

theorem interlacing_defect_eq_card (hI : Interlace h lam sg) :
    D1 h lam sg = ((∑ i : Fin n, ((Rset h lam sg i).erase (sg.w i)).card : ℕ) : ℤ) := by
  unfold D1
  push_cast
  exact Finset.sum_congr rfl (fun i _ => (card_R_erase h lam sg hI i).symm)

theorem interlacing_defect_nonneg (hI : Interlace h lam sg) : 0 ≤ D1 h lam sg := by
  rw [interlacing_defect_eq_card h lam sg hI]
  exact Nat.cast_nonneg _

theorem mem_R_bounds (hI : Interlace h lam sg) (hn : 0 < n) (i : Fin n) (v : ℤ)
    (hv : v ∈ Rset h lam sg i) :
    lam.w ⟨N - 1, by omega⟩ ≤ v ∧
      v ≤ sg.w ⟨0, hn⟩ + (sg.w ⟨0, hn⟩ - lam.w ⟨N - 1, by omega⟩) := by
  unfold Rset at hv
  rw [Finset.mem_Icc] at hv
  have h1 := lam_le_last h lam (i.1 + 1) (by omega)
  have h2 := (hI i).2
  have h3 := sg_le_first sg hn i
  have h4 := interlacing_defect_le_gap h lam sg hI hn
  have h5 := min_le_right (lam.w ⟨i.1, by omega⟩) (lam.w ⟨i.1 + 1, by omega⟩ + D0 h lam sg)
  constructor <;> omega

end PI.GTNum
