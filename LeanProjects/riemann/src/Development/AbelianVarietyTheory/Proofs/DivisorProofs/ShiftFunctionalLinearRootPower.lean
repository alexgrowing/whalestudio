import Mathlib
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl

open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly

namespace GlobalTheory.FlagPoly.DerivPow

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

theorem pderiv_linRoot (u : ι → Fin N → ℝ) (x : ι × Fin N) :
    pderiv x (linRoot u) = C (-(u x.1 x.2)) := by
  simp [linRoot, pderiv_X, Pi.single_apply]

theorem degFl_pderiv_pow (u : ι → Fin N → ℝ) (τ : ι) (i : Fin N) :
    degFl ι N (pderiv (τ, i) (linRoot u ^ (dimFl ι N + 1))) =
      -((dimFl ι N : ℝ) + 1) * flagDeg ι N u * u τ i := by
  have h : pderiv (τ, i) (linRoot u ^ (dimFl ι N + 1)) =
      C (-((dimFl ι N : ℝ) + 1) * u τ i) * linRoot u ^ dimFl ι N := by
    rw [pderiv_pow, pderiv_linRoot]
    simp only [Nat.add_sub_cancel, map_mul, map_neg, map_add, map_natCast, map_one, Nat.cast_add,
      Nat.cast_one]
    ring
  rw [h, PPowSum.degFl_C_mul, flagDeg]
  ring

theorem shF_totF_linRoot_pow :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (j : ℕ) (u : ι → Fin N → ℝ) (τ : ι), shF j τ (linRoot u ^ (dimFl ι N + 1)) = -((dimFl ι N : ℝ) + 1) * flagDeg ι N u * ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), u τ i ∧ totF τ (linRoot u ^ (dimFl ι N + 1)) = -((dimFl ι N : ℝ) + 1) * flagDeg ι N u * ∑ i : Fin N, u τ i := by
  intro ι _ _ N j u τ
  constructor
  · rw [shF, PPowSum.degFl_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => degFl_pderiv_pow u τ i
  · rw [totF, PPowSum.degFl_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => degFl_pderiv_pow u τ i

end GlobalTheory.FlagPoly.DerivPow
