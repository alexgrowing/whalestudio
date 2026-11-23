import Formalism.BranchSandwichDivisors.StatementR

open Finset

namespace Formalism.BranchingDeterminantCap

theorem degreeTransferBound : TransferDeg := by
  unfold TransferDeg
  intro S _ rk nS dgA dgB la degP h1 h2 h3 hla hR
  have hR0 : 0 ≤ ∑ s, nS s * rk s := Finset.sum_nonneg fun s _ => hR s
  have hBA : |∑ s, dgB s - ∑ s, nS s * dgA s| ≤ 13 / 2 * la * ∑ s, nS s * rk s := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => h1 s)
  have hlR : 0 ≤ la * ∑ s, nS s * rk s := mul_nonneg hla hR0
  rw [abs_le] at hBA ⊢
  obtain ⟨hBA1, hBA2⟩ := hBA
  constructor <;> linarith

theorem meanTransferBound : TransferMean := by
  unfold TransferMean
  intro S _ rk nS dg nbar de la ka HH0 muP0 muPs muR0 muRs hnbar hde0 hde13 hla hka hrk hR hn
    hR0 hRs hdg hPs hP0
  rw [abs_le] at hR0 hRs
  obtain ⟨hR0a, hR0b⟩ := hR0
  obtain ⟨hRsa, hRsb⟩ := hRs
  have hD : ∑ s, dg s ≤ (∑ s, rk s) * (HH0 + ka * la) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun s _ => hdg s
  have hWlo : (1 - de) * nbar * ∑ s, rk s ≤ ∑ s, nS s * rk s := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right (hn s).1 (hrk s)
  have hmuP0 : muP0 ≤ HH0 + ka * la + 2 * la := by
    have h : muP0 * ∑ s, rk s ≤ (HH0 + ka * la + 2 * la) * ∑ s, rk s := by linarith
    exact le_of_mul_le_mul_right h hR
  refine ⟨by linarith, ?_⟩
  have hW : 0 < ∑ s, nS s * rk s := by
    have : 0 < (1 - de) * nbar * ∑ s, rk s := mul_pos (mul_pos (by linarith) hnbar) hR
    linarith
  have key : ∑ s, ((HH0 + ka * la) * (nS s * rk s) - (1 + de) * nbar * ((HH0 + ka * la) * rk s)
      + (1 + de) * nbar * dg s) ≤ ∑ s, nS s * dg s := by
    refine Finset.sum_le_sum fun s _ => ?_
    nlinarith [mul_nonneg (sub_nonneg.2 (hdg s)) (sub_nonneg.2 (hn s).2)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at key
  have hnn : 0 ≤ (1 + de) * nbar := mul_nonneg (by linarith) hnbar.le
  have h3 : (1 + de) * nbar * (muP0 * ∑ s, rk s) ≤
      (1 + de) * nbar * ((∑ s, dg s) + 2 * la * ∑ s, rk s) :=
    mul_le_mul_of_nonneg_left hP0 hnn
  have hY : 0 ≤ (1 + 3 * de) * (HH0 + ka * la + 2 * la - muP0) :=
    mul_nonneg (by linarith) (by linarith)
  have h1 : (1 + 3 * de) * (HH0 + ka * la + 2 * la - muP0) * ((1 - de) * nbar * ∑ s, rk s) ≤
      (1 + 3 * de) * (HH0 + ka * la + 2 * la - muP0) * ∑ s, nS s * rk s :=
    mul_le_mul_of_nonneg_left hWlo hY
  have h2 : 0 ≤ (HH0 + ka * la + 2 * la - muP0) * nbar * (∑ s, rk s) * (de * (1 - 3 * de)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hnbar.le) hR.le)
      (mul_nonneg hde0 (by linarith))
  have hmain : (-muPs) * ∑ s, nS s * rk s ≤
      (17 / 2 * la - (HH0 + ka * la) + (1 + 3 * de) * (HH0 + ka * la + 2 * la - muP0)) *
        ∑ s, nS s * rk s := by
    linarith
  have hmuPs := le_of_mul_le_mul_right hmain hW
  have hXY : 3 * de * (HH0 + ka * la + 2 * la - muP0) ≤
      3 * de * (-muR0 + HH0 + (2 * ka + 2) * la) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith

theorem meanShiftAssembly : PassageAssembly := by
  unfold PassageAssembly
  intro S _ rk nS dg nbar lam0 HH0 muP0 muPs mu0 muC f r g Q C0 hnbar hlam0 hrk hR hf hr hg hn
    h0 hC hdg hPs hP0 hZQ hQ hfrQ hC0
  have hde0 : 0 ≤ 8 * f * r / g :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hf) hr) hg.le
  have hdeQ : 8 * f * r / g * (3 * Q) ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hg]
    linarith
  have hMT := meanTransferBound
  unfold TransferMean at hMT
  set de := 8 * f * r / g with hde
  have hde13 : de ≤ 1 / 3 := by nlinarith [mul_nonneg hde0 (sub_nonneg.2 hQ)]
  obtain ⟨_, hB⟩ := hMT S rk nS dg nbar de lam0 1 HH0 muP0 muPs (-mu0) (-muC) hnbar hde0 hde13
    hlam0 zero_le_one hrk hR hn (by rw [one_mul]; exact h0) (by rw [one_mul]; exact hC)
    (fun s => by rw [one_mul]; exact hdg s) hPs hP0
  have hZ : 3 * de * (mu0 + HH0 + 4 * lam0) ≤ 3 * de * Q :=
    mul_le_mul_of_nonneg_left hZQ (by linarith)
  have hC' : 0 ≤ (C0 - 25 / 2) * lam0 := mul_nonneg (by linarith) hlam0
  constructor <;> linarith

end Formalism.BranchingDeterminantCap
