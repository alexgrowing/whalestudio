import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightPositiveDiagonalLeSumAddInv
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_positiveDiagonal_le_sum_add_inv : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → height d ≤ 1 + ∑ i, r i + ∑ i, (r i)⁻¹ := by
  first | exact @GlobalTheory.height_diagonal_le_sum | exact GlobalTheory.height_diagonal_le_sum | (intros; apply GlobalTheory.height_diagonal_le_sum <;> assumption)
