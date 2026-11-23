import Mathlib
import Formalism.PeriodIntegrals.GTDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinTopCoefficient.CardEraseIccMin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinTopCoefficient.InterlacingDefectEqCard

noncomputable section

namespace PI.GTNum

open Formalism.BasicNotions PI Finset

variable {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)

theorem sg_le_top (hI : Interlace h lam sg) (j : Fin n) : sg.w j ≤ lam.w ⟨0, by omega⟩ :=
  le_trans (hI j).1 (lam.anti (Fin.mk_le_mk.2 (Nat.zero_le _)))

theorem mem_R_bounds_top (i : Fin n) (v : ℤ) (hv : v ∈ Rset h lam sg i) :
    lam.w ⟨N - 1, by omega⟩ ≤ v ∧ v ≤ lam.w ⟨0, by omega⟩ := by
  unfold Rset at hv
  rw [Finset.mem_Icc] at hv
  have h1 := lam_le_last h lam (i.1 + 1) (by omega)
  have h2 : lam.w ⟨i.1, by omega⟩ ≤ lam.w ⟨0, by omega⟩ := lam.anti (Fin.mk_le_mk.2 (Nat.zero_le _))
  have h5 := min_le_left (lam.w ⟨i.1, by omega⟩) (lam.w ⟨i.1 + 1, by omega⟩ + D0 h lam sg)
  constructor <;> omega

theorem cBr_ne_zero (hI : Interlace h lam sg) : cBr h lam sg ≠ 0 := by
  unfold cBr
  refine Finset.prod_ne_zero_iff.2 (fun i _ => Finset.prod_ne_zero_iff.2 (fun v hv =>
    Finset.prod_ne_zero_iff.2 (fun j _ => ?_)))
  have hvs : v ≠ sg.w i := Finset.ne_of_mem_erase hv
  have hvR := Finset.mem_of_mem_erase hv
  unfold Rset at hvR
  rw [Finset.mem_Icc] at hvR
  have h5 := min_le_left (lam.w ⟨i.1, by omega⟩) (lam.w ⟨i.1 + 1, by omega⟩ + D0 h lam sg)
  rcases lt_trichotomy j.1 i.1 with hji | hji | hji
  · have a1 : lam.w ⟨i.1, by omega⟩ ≤ lam.w ⟨j.1 + 1, by omega⟩ := lam.anti (Fin.mk_le_mk.2 (by omega))
    have a2 := (hI j).2
    omega
  · have e : j = i := Fin.ext hji
    subst e
    omega
  · have a1 : lam.w ⟨j.1, by omega⟩ ≤ lam.w ⟨i.1 + 1, by omega⟩ := lam.anti (Fin.mk_le_mk.2 (by omega))
    have a2 := (hI j).1
    omega

theorem abs_cBr_le_top (hI : Interlace h lam sg) :
    |cBr h lam sg| ≤ (lam.w ⟨0, by omega⟩ - lam.w ⟨N - 1, by omega⟩ + (n : ℤ)) ^
      (n * ∑ i : Fin n, ((Rset h lam sg i).erase (sg.w i)).card) := by
  unfold cBr
  rw [← prod_pow_pow]
  refine abs_prod_le_prod _ _ _ (fun i _ => ?_)
  refine abs_prod_le_pow _ _ _ (fun v hv => ?_)
  have hc : ((lam.w ⟨0, by omega⟩ - lam.w ⟨N - 1, by omega⟩ + (n : ℤ)) ^ n) =
      (lam.w ⟨0, by omega⟩ - lam.w ⟨N - 1, by omega⟩ + (n : ℤ)) ^ (univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
  rw [hc]
  refine abs_prod_le_pow _ _ _ (fun j _ => ?_)
  have hv' := mem_R_bounds_top h lam sg i v (Finset.mem_of_mem_erase hv)
  have hs1 := last_le_sg h lam sg hI j
  have hs2 := sg_le_top h lam sg hI j
  have hi := i.2
  have hj := j.2
  rw [abs_le]
  constructor <;> omega

theorem abs_cBr_le_cBd (hI : Interlace h lam sg) :
    |((cBr h lam sg : ℤ) : ℝ)| ≤ cBd h lam sg := by
  set K : ℕ := ∑ i : Fin n, ((Rset h lam sg i).erase (sg.w i)).card with hK
  have hD1 : (N : ℤ) * D1 h lam sg = ((N * K : ℕ) : ℤ) := by
    rw [interlacing_defect_eq_card h lam sg hI, ← hK, Nat.cast_mul]
  have hN : 0 < N := by omega
  have hsp : lam.spread = lam.w ⟨0, by omega⟩ - lam.w ⟨N - 1, by omega⟩ + N := by
    unfold DomWeight.spread
    rw [dif_pos hN]
  have hlast := lam_le_last h lam 0 (by omega)
  have hb := abs_cBr_le_top h lam sg hI
  rw [← hK] at hb
  have hb2 : (lam.w ⟨0, by omega⟩ - lam.w ⟨N - 1, by omega⟩ + (n : ℤ)) ^ (n * K) ≤
      (2 * lam.spread) ^ (N * K) := by
    calc (lam.w ⟨0, by omega⟩ - lam.w ⟨N - 1, by omega⟩ + (n : ℤ)) ^ (n * K)
        ≤ (2 * lam.spread) ^ (n * K) := by
          apply pow_le_pow_left₀ (by omega)
          rw [hsp]
          omega
      _ ≤ (2 * lam.spread) ^ (N * K) := by
          apply pow_le_pow_right₀ (by rw [hsp]; omega)
          exact Nat.mul_le_mul_right K (by omega)
  unfold cBd
  rw [hD1, Int.cast_natCast, Real.rpow_natCast, ← Int.cast_abs]
  exact_mod_cast le_trans hb hb2

theorem degZ_eq : degZ lam sg = lam.w ⟨0, by omega⟩ - D0 h lam sg := by
  subst h
  unfold degZ wsum D0
  rw [Fin.sum_univ_succ, Finset.sum_sub_distrib]
  have e1 : ∑ i : Fin n, lam.w i.succ = ∑ i : Fin n, lam.w ⟨i.1 + 1, by omega⟩ := rfl
  have e0 : lam.w 0 = lam.w ⟨0, by omega⟩ := rfl
  rw [e1, e0]
  ring

end PI.GTNum
