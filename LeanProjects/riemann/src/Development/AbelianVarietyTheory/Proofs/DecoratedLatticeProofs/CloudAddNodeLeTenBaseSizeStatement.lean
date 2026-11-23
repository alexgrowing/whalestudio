import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CloudAddNodeLeTenBaseSize
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Formalism.SharpRestriction.ElevenLe
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cloud_add_node_le_ten_base_size : ∀ (C : Formalism.MainNotions.Inhab.FC) (cD ch : ℝ) (D : D7) (L : SizeData₂ D), Val C cD ch L → SizesAt L → L.sc.x ≤ L.sc.X' → ∀ τ : D.what₂.Tau, (∀ i j, (((D.hc τ).v i : ℚ) : ℝ) + (((D.hc τ).b j : ℚ) : ℝ) ≤ 10 * L.sc.b) ∧ ∀ j j', (((D.hc τ).b j' : ℚ) : ℝ) - (((D.hc τ).b j : ℚ) : ℝ) ≤ 10 * L.sc.b := by
  first | exact @GlobalTheory.cloud_add_node_le_ten_b | exact GlobalTheory.cloud_add_node_le_ten_b | (intros; apply GlobalTheory.cloud_add_node_le_ten_b <;> assumption)
