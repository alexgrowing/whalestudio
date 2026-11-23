import Mathlib
import Formalism.PeriodIntegrals.GTCoefTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinTopCoefficient.CardEraseIccMin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinTopCoefficient.InterlacingDefectEqCard

noncomputable section

namespace PI.GTNum

open Formalism.BasicNotions PI Finset

theorem abs_cBr_le {n N : ℕ} (h : n + 1 = N) (hn : 0 < n) (lam : DomWeight N) (sg : DomWeight n)
    (hI : Interlace h lam sg) :
    |cBr h lam sg| ≤ (2 * (sg.w ⟨0, hn⟩ - lam.w ⟨N - 1, by omega⟩) + (N : ℤ)) ^
      (n * ∑ i : Fin n, ((Rset h lam sg i).erase (sg.w i)).card) := by
  set B : ℤ := 2 * (sg.w ⟨0, hn⟩ - lam.w ⟨N - 1, by omega⟩) + (N : ℤ) with hB
  unfold cBr
  rw [← prod_pow_pow]
  refine abs_prod_le_prod _ _ _ (fun i _ => ?_)
  refine abs_prod_le_pow _ _ _ (fun v hv => ?_)
  have hc : (B ^ n) = B ^ (univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
  rw [hc]
  refine abs_prod_le_pow _ _ _ (fun j _ => ?_)
  have hv' := mem_R_bounds h lam sg hI hn i v (Finset.mem_of_mem_erase hv)
  have hs1 := last_le_sg h lam sg hI j
  have hs2 := sg_le_first sg hn j
  have := abs_factor_le v (sg.w j) (lam.w ⟨N - 1, by omega⟩) (sg.w ⟨0, hn⟩) i.1 j.1 n i.2 j.2
    hv'.1 hv'.2 hs1 hs2
  have hN : ((n + 1 : ℕ) : ℤ) = (N : ℤ) := by rw [h]
  rw [hN] at this
  rw [hB]
  exact this

theorem top_indep {n N : ℕ} (h : n + 1 = N) (hn : 0 < n) (lam lam' : DomWeight N) (sg : DomWeight n)
    (hag : ∀ i : Fin N, i.1 ≠ 0 → lam'.w i = lam.w i)
    (htop : lam.w ⟨1, by omega⟩ + D0 h lam sg ≤ lam.w ⟨0, by omega⟩)
    (htop' : lam'.w ⟨1, by omega⟩ + D0 h lam' sg ≤ lam'.w ⟨0, by omega⟩) :
    cBr h lam' sg = cBr h lam sg ∧ D1 h lam' sg = D1 h lam sg := by
  have hD0 : D0 h lam' sg = D0 h lam sg := by
    unfold D0
    exact Finset.sum_congr rfl (fun i _ => by rw [hag _ (Nat.succ_ne_zero _)])
  have h1 : lam'.w ⟨1, by omega⟩ = lam.w ⟨1, by omega⟩ := hag _ (Nat.succ_ne_zero _)
  have key : ∀ i : Fin n,
      min (lam'.w ⟨i.1, by omega⟩) (lam'.w ⟨i.1 + 1, by omega⟩ + D0 h lam' sg) =
        min (lam.w ⟨i.1, by omega⟩) (lam.w ⟨i.1 + 1, by omega⟩ + D0 h lam sg) ∧
      lam'.w ⟨i.1 + 1, by omega⟩ = lam.w ⟨i.1 + 1, by omega⟩ ∧
      min (lam'.w ⟨i.1, by omega⟩ - lam'.w ⟨i.1 + 1, by omega⟩) (D0 h lam' sg) =
        min (lam.w ⟨i.1, by omega⟩ - lam.w ⟨i.1 + 1, by omega⟩) (D0 h lam sg) := by
    intro i
    have e1 : lam'.w ⟨i.1 + 1, by omega⟩ = lam.w ⟨i.1 + 1, by omega⟩ := hag _ (Nat.succ_ne_zero _)
    by_cases hi : i.1 = 0
    · have a0 : lam'.w ⟨i.1, by omega⟩ = lam'.w ⟨0, by omega⟩ := congrArg lam'.w (Fin.ext hi)
      have b0 : lam.w ⟨i.1, by omega⟩ = lam.w ⟨0, by omega⟩ := congrArg lam.w (Fin.ext hi)
      have b1 : lam.w ⟨i.1 + 1, by omega⟩ = lam.w ⟨1, by omega⟩ :=
        congrArg lam.w (Fin.ext (by simp [hi]))
      refine ⟨?_, e1, ?_⟩ <;> omega
    · have e0 : lam'.w ⟨i.1, by omega⟩ = lam.w ⟨i.1, by omega⟩ := hag _ hi
      rw [e0, e1, hD0]
      exact ⟨rfl, rfl, rfl⟩
  have hR : ∀ i : Fin n, Rset h lam' sg i = Rset h lam sg i := by
    intro i
    unfold Rset
    rw [(key i).1, (key i).2.1]
  constructor
  · unfold cBr
    exact Finset.prod_congr rfl (fun i _ => by rw [hR i])
  · unfold D1
    exact Finset.sum_congr rfl (fun i _ => (key i).2.2)

theorem gTCoefTop_main : PI.GTCoefTop := by
  intro n N h hn lam sg hI htop
  refine ⟨?_, fun lam' hag htop' => top_indep h hn lam lam' sg hag htop htop'⟩
  set K : ℕ := ∑ i : Fin n, ((Rset h lam sg i).erase (sg.w i)).card with hK
  have hD1 : (n : ℤ) * D1 h lam sg = ((n * K : ℕ) : ℤ) := by
    rw [interlacing_defect_eq_card h lam sg hI, ← hK, Nat.cast_mul]
  have hb := abs_cBr_le h hn lam sg hI
  rw [hD1, Int.cast_natCast, Real.rpow_natCast, ← Int.cast_abs]
  exact_mod_cast hb

end PI.GTNum
