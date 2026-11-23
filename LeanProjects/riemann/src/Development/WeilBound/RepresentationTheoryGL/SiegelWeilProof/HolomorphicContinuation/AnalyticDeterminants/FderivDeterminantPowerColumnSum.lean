import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.AnalyticAtDeterminantPowerZeroInt

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.CK

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {N : ℕ}

def fsum (t : ℤ) (c : Fin N) (X : Matrix (Fin N) (Fin (N + 1)) ℂ) : ℂ :=
  -∑ k, X k 0 * fderiv ℂ (H N t) (piF X) (Matrix.single k c 1)

theorem colQ_expand (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (c : Fin N) :
    colQ X c = ∑ k, X k 0 • Matrix.single k c (1 : ℂ) := by
  ext k l
  simp only [colQ, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  split_ifs with h
  · subst h
    simp
  · simp [Ne.symm h]

theorem fderiv_determinant_power_column_sum (t : ℤ) (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (hX : (1 + piF X).det ≠ 0) (c : Fin N) :
    fderiv ℂ (H (N + 1) t) (phiF X) (Matrix.single 0 c.succ 1) = fsum t c X := by
  rw [fderiv_determinant_power_column_int t X hX c, colQ_expand, map_sum, fsum]
  simp only [map_smul, smul_eq_mul]

theorem analyticAt_entry (k : Fin N) (j : Fin (N + 1)) (X0 : Matrix (Fin N) (Fin (N + 1)) ℂ) :
    AnalyticAt ℂ (fun X : Matrix (Fin N) (Fin (N + 1)) ℂ => X k j) X0 := by
  have := (LinearMap.toContinuousLinearMap
    (Matrix.entryLinearMap ℂ ℂ k j : Matrix (Fin N) (Fin (N + 1)) ℂ →ₗ[ℂ] ℂ)).analyticAt X0
  exact this

theorem analyticAt_piF (X0 : Matrix (Fin N) (Fin (N + 1)) ℂ) :
    AnalyticAt ℂ (piF : Matrix (Fin N) (Fin (N + 1)) ℂ → Matrix (Fin N) (Fin N) ℂ) X0 :=
  (piL N).analyticAt X0

theorem analyticAt_fsum (t : ℤ) (c : Fin N) (X0 : Matrix (Fin N) (Fin (N + 1)) ℂ) (h : (1 + piF X0).det ≠ 0) :
    AnalyticAt ℂ (fsum t c) X0 := by
  have hE : ∀ k : Fin N, AnalyticAt ℂ (fun X : Matrix (Fin N) (Fin (N + 1)) ℂ =>
      X k 0 * fderiv ℂ (H N t) (piF X) (Matrix.single k c 1)) X0 := by
    intro k
    refine (analyticAt_entry k 0 X0).mul ?_
    exact (analyticAt_fderiv_apply (H N t) (piF X0) (Matrix.single k c 1)
      (analyticAt_H N t _ h)).comp (analyticAt_piF X0)
  have hs := (Finset.analyticAt_sum Finset.univ (fun k _ => hE k)).neg
  convert hs using 1
  funext X
  simp [fsum, Finset.sum_apply]

end PositivityTheory.Rg.Sw.LVs.CK
