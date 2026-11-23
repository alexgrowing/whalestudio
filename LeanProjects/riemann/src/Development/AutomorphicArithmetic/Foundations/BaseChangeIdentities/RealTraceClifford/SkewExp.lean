import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.RealTrOfAll
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryExistsSkewLog

noncomputable section

open MeasureTheory Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace ComplexConjugate ContDiff
open PositivityTheory.RgTw (Mat G th IsThetaOp)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem UpperTheory.RealTr.skewExp :
    ∀ n : ℕ, (∀ X : Mat n, Xᴴ = -X → NormedSpace.exp X ∈ Matrix.unitaryGroup (Fin n) ℂ) ∧
      ∀ k : UK n, ∃ X : Mat n, Xᴴ = -X ∧ NormedSpace.exp X = k.1 := by
  intro n
  refine ⟨fun X hX => ?_, fun k => ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    change NormedSpace.exp X * (NormedSpace.exp X)ᴴ = 1
    rw [← Matrix.exp_conjTranspose, hX,
      ← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl X)), add_neg_cancel,
      NormedSpace.exp_zero]
  · obtain ⟨X, p, hX, hk, -⟩ := GlobalTheory.unitary_exists_skew_log n k.1 (Matrix.mem_unitaryGroup_iff'.mp k.2)
    exact ⟨X, hX, hk⟩
