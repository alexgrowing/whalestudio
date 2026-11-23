import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthNonnegIntegralOperatorIntegralVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialOperatorDepthLeDividedPowerContentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixVariablesDeterminantPowMonomialShapeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerContentValuationDetPowBoundsStatement
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem natCast_isInt {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℕ) :
    0 ≤ v (n : C) := by
  induction n with
  | zero => simp
  | succ k ih =>
    push_cast
    refine le_trans (le_min ih (by simp)) (v.map_add _ _)

theorem intCast_isInt {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℤ) :
    0 ≤ v (n : C) := by
  cases n with
  | ofNat k => simpa using natCast_isInt v k
  | negSucc k =>
    rw [Int.cast_negSucc, v.map_neg]
    exact_mod_cast natCast_isInt v (k + 1)

theorem detDepth_bounds : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (i d c : ℕ) (G : LogFGL v d) (u : Fin i → Fin d → C),
    IsSatFrame v u → 0 ≤ detDepth G u c ∧ detDepth G u c ≤ content v (detPow C i c) ∧
    detDepth G u c ≤ (((i * c : ℝ) / (p - 1) : ℝ) : EReal) := by
  intro C _ _ v p hp hv i d c G u hu
  obtain ⟨hhom, hint, -, -⟩ := GlobalTheory.T.matrixVariablesDeterminantPow_monomial_shape C i c
  have h0 : 0 ≤ detDepth G u c := by
    unfold detDepth
    exact GlobalTheory.T.depth_nonneg_integral_operator_integral_vectors C v (Fin i) (fun _ => d) (fun _ => G) (fun _ => Fin i) (fun _ => u)
      (detPow C i c) (fun _ a e => hu.1 a e)
      (fun α => by obtain ⟨n, hn⟩ := hint α; rw [hn]; exact intCast_isInt v n)
  have h1 : detDepth G u c ≤ content v (detPow C i c) := by
    unfold detDepth
    exact GlobalTheory.T.differentialOperatorDepth_le_dividedPowerContent C v (Fin i) (fun _ => d) (fun _ => i) (fun _ => G) (fun _ => u)
      (detPow C i c) (i * c) hhom (fun _ => hu)
  exact ⟨h0, h1, h1.trans (GlobalTheory.T.dividedPowerContentValuation_detPow_bounds C v p hp hv i c).1⟩

end GlobalTheory.FGDepth
