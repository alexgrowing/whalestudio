import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetOpIntegral
import Formalism.LocalToGlobal.Columns.BaseLemmas

noncomputable section

namespace GlobalTheory.ColPeriod

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recWts)

theorem nuRow_succ_eq_wt (D : D7) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m) (τ : D.what₂.Tau) (n : ℕ) (hn : n < D.R.N j) :
    DV.nuRow D u (j + 1) τ n =
      ((Examples₂.wtN (D.hcW u τ) n + wG D.R ((D.hcW u τ).e ⟨j, hj⟩) (j + 1) : ℚ) : ℝ) := by
  have hw : DV.wSz D (j + 1) τ = (((D.hcW u τ).e ⟨j, hj⟩ : ℚ) : ℝ) := by
    unfold DV.wSz
    rw [dif_pos ⟨by omega, by omega⟩, D.hcW_e]
    rfl
  unfold DV.nuRow
  rw [hw]
  unfold DV.srcPar Examples₂.wtN Examples₂.blkN
  by_cases hk : n < D.R.k
  · rw [dif_pos hk, dif_pos hk]
    unfold hcToWeightQ rhoVec wG Ranks.N
    push_cast
    ring
  · have hb : (n - D.R.k) / (D.R.t + 1) < D.R.m := by
      have hN : n < D.R.k + j * (D.R.t + 1) := hn
      have h2 : n - D.R.k < j * (D.R.t + 1) := Nat.sub_lt_left_of_lt_add (by omega) hN
      have h3 : (n - D.R.k) / (D.R.t + 1) < j := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact h2)
      omega
    rw [dif_neg hk, dif_neg hk, dif_pos hb, dif_pos hb]
    have hnat : n = D.R.k + (n - D.R.k) / (D.R.t + 1) * (D.R.t + 1) + (n - D.R.k) % (D.R.t + 1) := by
      have := Nat.div_add_mod (n - D.R.k) (D.R.t + 1)
      rw [mul_comm] at this
      omega
    have key : (n : ℝ) = (D.R.k : ℝ) + (((n - D.R.k) / (D.R.t + 1) : ℕ) : ℝ) * ((D.R.t : ℝ) + 1)
        + (((n - D.R.k) % (D.R.t + 1) : ℕ) : ℝ) := by
      conv_lhs => rw [hnat]
      push_cast
      ring
    unfold wG Ranks.N
    push_cast
    linear_combination key

theorem partitionSize : PartitionSize := by
  intro D EX u j hj τ
  unfold nuAbs
  show ∑ i ∈ Finset.range (D.R.N j), DV.nuRow D u (j + 1) τ i = _
  rw [Finset.sum_range, Int.cast_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [nuRow_succ_eq_wt D u j hj τ a a.2]
  have h1 := Wts.nuW_eq (recWts EX) u hj τ a
  have h2 := lamOf_wtN ((recWts EX).hc u τ) hj.le a
  have h3 : (((recWts EX).nuW u (j + 1) τ).w a : ℝ) = ((((recWts EX).nuW u (j + 1) τ).w a : ℚ) : ℝ) := by
    simp
  rw [h3, h1]
  unfold Wts.lamN
  rw [h2]
  rfl

end GlobalTheory.ColPeriod
