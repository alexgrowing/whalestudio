import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgePowerEqFactorialDet
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wedge_power_eq_factorial_det : ∀ {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] (α : T [⋀^Fin 2]→L[ℝ] ℝ) (g : ℕ) (v : Fin g × Fin 2 → T) (S : Matrix (Fin g) (Fin g) ℝ), (∀ i j, α ![v (i, 0), v (j, 0)] = 0) → (∀ i j, α ![v (i, 1), v (j, 1)] = 0) → (∀ i j, α ![v (i, 0), v (j, 1)] = S i j) → wedgePow α g v = (g.factorial : ℝ) * S.det := by
  first | exact @GlobalTheory.wedgePow_block_eq | exact GlobalTheory.wedgePow_block_eq | (intros; apply GlobalTheory.wedgePow_block_eq <;> assumption)
