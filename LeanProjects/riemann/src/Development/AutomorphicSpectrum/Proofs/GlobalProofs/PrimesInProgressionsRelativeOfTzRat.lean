import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsExcRat
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.PrimesInProgressionsRelative
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LFunctionConjEqZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ZeroFreePrincipal

open Finset DirichletCharacter
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.PrimesAP

def fibre {N M : ℕ} [NeZero M] (h : N ∣ M) (a : (ZMod N)ˣ) : Finset (ZMod M)ˣ :=
  Finset.univ.filter (fun u => ZMod.unitsMap h u = a)

theorem intervalIntegrable_inv_log {Y X : ℝ} (hY : 2 ≤ Y) (hX : 2 ≤ X) :
    IntervalIntegrable (fun t => 1 / Real.log t) MeasureTheory.volume Y X := by
  apply ContinuousOn.intervalIntegrable
  have : ∀ t ∈ Set.uIcc Y X, 2 ≤ t := fun t ht => le_trans (le_min hY hX) ht.1
  refine continuousOn_const.div (Real.continuousOn_log.mono ?_) ?_
  · intro t ht
    have := this t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith [this]
  · intro t ht
    exact (Real.log_pos (by linarith [this t ht])).ne'

theorem le_integral_inv_log {Y X : ℝ} (hY : 2 ≤ Y) (hX : Y ≤ X) :
    (X - Y) / Real.log X ≤ ∫ t in Y..X, 1 / Real.log t := by
  have : (X - Y) / Real.log X = ∫ _ in Y..X, 1 / Real.log X := by
    simp [div_eq_mul_inv]
  rw [this]
  apply intervalIntegral.integral_mono_on hX (by simp) (intervalIntegrable_inv_log hY (hY.trans hX))
  intro t ht
  exact one_div_le_one_div_of_le (Real.log_pos (by linarith [ht.1])) (Real.log_le_log (by linarith [ht.1]) ht.2)

end GlobalTheory.CompanionTheory.PrimesAP
