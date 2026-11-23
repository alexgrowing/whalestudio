import Mathlib
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftFunctionalPowerSumStatement

open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly

namespace GlobalTheory.FlagPoly.TestClass

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

theorem shF_sum (j : ℕ) (σ : ι) (F : ι → Pol ι N) :
    shF j σ (∑ τ, F τ) = ∑ τ, shF j σ (F τ) := by
  unfold shF
  simp only [map_sum]
  rw [Finset.sum_comm, PPowSum.degFl_sum]

theorem totF_sum (σ : ι) (F : ι → Pol ι N) :
    totF σ (∑ τ, F τ) = ∑ τ, totF σ (F τ) := by
  unfold totF
  simp only [map_sum]
  rw [Finset.sum_comm, PPowSum.degFl_sum]

theorem pLow_add_pHigh (j : ℕ) (τ : ι) (k : ℕ) :
    (pLow j τ k + pHigh j τ k : Pol ι N) = pSum τ k := by
  unfold pLow pHigh pSum
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin N => (i : ℕ) < j)]
  simp only [not_lt]

theorem degFl_lamA_mul (j : ℕ) (Q : Pol ι N) :
    degFl ι N (lamA ι N j * Q) = -2 * ∑ τ : ι, degFl ι N (pLow j τ 1 * Q) := by
  unfold lamA
  rw [Finset.sum_mul, PPowSum.degFl_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h : (pHigh j τ 1 - pLow j τ 1) * Q = pSum τ 1 * Q + C (-2 : ℝ) * (pLow j τ 1 * Q) := by
    rw [← pLow_add_pHigh j τ 1, map_neg, map_ofNat]; ring
  have h0 : degFl ι N (pSum τ 1 * Q) = 0 := degreePowerSumMulEqZero ι N τ 1 Q le_rfl
  rw [h, PPowSum.degFl_add, PPowSum.degFl_C_mul, h0, zero_add]

theorem lamA_homog (j : ℕ) : (lamA ι N j).IsHomogeneous 1 := by
  unfold lamA pHigh pLow
  refine IsHomogeneous.sum _ _ _ fun τ _ => IsHomogeneous.sub ?_ ?_ <;>
  exact IsHomogeneous.sum _ _ _ fun i _ => by simpa using isHomogeneous_X ℝ (τ, i)

theorem sum_fibExp (j : ℕ) (hj : j ≤ N) :
    (∑ i : Fin N, (if (i : ℕ) < j then j - 1 - (i : ℕ) else N - 1 - (i : ℕ))) + j * (N - j)
      = N * (N - 1) / 2 := by
  have h1 : ∑ i : Fin N, (if (i : ℕ) < j then N - j else 0) = j * (N - j) := by
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, Fin.card_filter_val_lt, min_eq_right hj]
  rw [← h1, ← Finset.sum_add_distrib, ← PermutationPointDegree.sum_delta N]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> omega

theorem fibPt_homog (j : ℕ) : (fibPt ι N j).IsHomogeneous
    (Fintype.card ι * ∑ i : Fin N, (if (i : ℕ) < j then j - 1 - (i : ℕ) else N - 1 - (i : ℕ))) := by
  unfold fibPt
  have := IsHomogeneous.prod (Finset.univ : Finset (ι × Fin N))
    (fun x => ((-X x : Pol ι N)) ^ (if (x.2 : ℕ) < j then j - 1 - (x.2 : ℕ) else N - 1 - (x.2 : ℕ)))
    (fun x => 1 * (if (x.2 : ℕ) < j then j - 1 - (x.2 : ℕ) else N - 1 - (x.2 : ℕ)))
    (fun x _ => (isHomogeneous_X ℝ x).neg.pow _)
  convert this using 1
  rw [Fintype.sum_prod_type]
  simp

theorem testClass : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) [Nonempty ι] (j : ℕ), 1 ≤ j → j < N → let I : ℝ := ∑ τ : ι, degFl ι N (pLow j τ 1 * curveCl ι N j); (∑ σ : ι, shF j σ (∑ τ : ι, pSum τ 2 * curveCl ι N j)) = 2 * I ∧ (∀ σ : ι, totF σ (∑ τ : ι, pSum τ 2 * curveCl ι N j) = 0) ∧ degFl ι N (lamA ι N j ^ dimGr ι N j * fibPt ι N j) = -2 * I ∧ degFl ι N (-lamA ι N j * curveCl ι N j) = 2 * I ∧ (curveCl ι N j).IsHomogeneous (dimFl ι N - 1) := by
  intro ι _ _ N _ j hj hjN I
  have hpos : 1 ≤ dimGr ι N j := by
    unfold dimGr
    exact Nat.mul_pos Fintype.card_pos (Nat.mul_pos hj (by omega))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [shF_sum, Finset.sum_congr rfl
      (fun τ _ => (GlobalTheory.T.shift_functional_power_sum ι N j 2 (curveCl ι N j) σ τ (by norm_num)).1)]
    simp
  · intro σ
    rw [totF_sum]
    refine Finset.sum_eq_zero fun τ _ => ?_
    rw [(GlobalTheory.T.shift_functional_power_sum ι N j 2 (curveCl ι N j) σ τ (by norm_num)).2]
    simp
  · have : lamA ι N j ^ dimGr ι N j * fibPt ι N j = lamA ι N j * curveCl ι N j := by
      unfold curveCl
      rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hpos]
    rw [this, degFl_lamA_mul]
  · have : -lamA ι N j * curveCl ι N j = C (-1 : ℝ) * (lamA ι N j * curveCl ι N j) := by
      rw [map_neg, map_one]; ring
    rw [this, PPowSum.degFl_C_mul, degFl_lamA_mul]; ring
  · unfold curveCl
    have := ((lamA_homog (ι := ι) (N := N) j).pow (dimGr ι N j - 1)).mul (fibPt_homog j)
    convert this using 1
    have h := congrArg (Fintype.card ι * ·) (sum_fibExp (N := N) j hjN.le)
    simp only [mul_add] at h
    unfold dimFl
    unfold dimGr at hpos ⊢
    omega

end GlobalTheory.FlagPoly.TestClass
