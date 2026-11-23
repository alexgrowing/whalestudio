import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

namespace GlobalTheory.Mean4.WholeShift

section Flag

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

theorem low_add_high (j : ℕ) (τ : ι) (k : ℕ) :
    (pLow j τ k + pHigh j τ k : Pol ι N) = pSum τ k := by
  unfold pLow pHigh pSum
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin N => (i : ℕ) < j)]
  simp only [not_lt]

theorem degFl_neg_lamA_mul (j : ℕ) (Q : Pol ι N) :
    degFl ι N (-lamA ι N j * Q) = 2 * ∑ τ : ι, degFl ι N (pLow j τ 1 * Q) := by
  unfold lamA
  rw [← Finset.sum_neg_distrib, Finset.sum_mul, PPowSum.degFl_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h : -(pHigh j τ 1 - pLow j τ 1) * Q = pSum τ 1 * (-Q) + C (2 : ℝ) * (pLow j τ 1 * Q) := by
    rw [← low_add_high j τ 1, map_ofNat]; ring
  have h0 : degFl ι N (pSum τ 1 * (-Q)) = 0 := degreePowerSumMulEqZero ι N τ 1 (-Q) le_rfl
  rw [h, PPowSum.degFl_add, PPowSum.degFl_C_mul, h0, zero_add]

theorem lamA_isHomogeneous (j : ℕ) : (lamA ι N j).IsHomogeneous 1 := by
  unfold lamA pHigh pLow
  refine IsHomogeneous.sum _ _ _ fun τ _ => IsHomogeneous.sub ?_ ?_ <;>
  exact IsHomogeneous.sum _ _ _ fun i _ => by simpa using isHomogeneous_X ℝ (τ, i)

theorem sum_exp (j : ℕ) (hj : j ≤ N) :
    (∑ i : Fin N, (if (i : ℕ) < j then j - 1 - (i : ℕ) else N - 1 - (i : ℕ))) + j * (N - j)
      = N * (N - 1) / 2 := by
  have h1 : ∑ i : Fin N, (if (i : ℕ) < j then N - j else 0) = j * (N - j) := by
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, Fin.card_filter_val_lt, min_eq_right hj]
  rw [← h1, ← Finset.sum_add_distrib, ← PermutationPointDegree.sum_delta N]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> omega

theorem fibPt_isHomogeneous (j : ℕ) : (fibPt ι N j).IsHomogeneous
    (Fintype.card ι * ∑ i : Fin N, (if (i : ℕ) < j then j - 1 - (i : ℕ) else N - 1 - (i : ℕ))) := by
  unfold fibPt
  have := IsHomogeneous.prod (Finset.univ : Finset (ι × Fin N))
    (fun x => ((-X x : Pol ι N)) ^ (if (x.2 : ℕ) < j then j - 1 - (x.2 : ℕ) else N - 1 - (x.2 : ℕ)))
    (fun x => 1 * (if (x.2 : ℕ) < j then j - 1 - (x.2 : ℕ) else N - 1 - (x.2 : ℕ)))
    (fun x _ => (isHomogeneous_X ℝ x).neg.pow _)
  convert this using 1
  rw [Fintype.sum_prod_type]
  simp

theorem curveCl_isHomogeneous (hι : 0 < Fintype.card ι) (j : ℕ) (hj : 1 ≤ j) (hjN : j < N) :
    ∃ m, m + 2 = dimFl ι N + 1 ∧ (curveCl ι N j).IsHomogeneous m := by
  have hpos : 1 ≤ dimGr ι N j := by
    unfold dimGr
    exact Nat.mul_pos hι (Nat.mul_pos hj (by omega))
  refine ⟨_, ?_, ((lamA_isHomogeneous (ι := ι) (N := N) j).pow (dimGr ι N j - 1)).mul (fibPt_isHomogeneous j)⟩
  have h := congrArg (Fintype.card ι * ·) (sum_exp (N := N) j hjN.le)
  simp only [mul_add] at h
  unfold dimFl
  unfold dimGr at hpos ⊢
  omega

end Flag

theorem chLieA_one (D : D7) (N j : ℕ) : chLieA D N j 1 = -lamA D.what₂.Tau N j := by
  unfold chLieA lamA
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [chLie, pHigh, pLow, Nat.factorial_one, Nat.cast_one, inv_one, map_one, one_mul, pow_one,
    Finset.sum_neg_distrib]
  ring

end GlobalTheory.Mean4.WholeShift
