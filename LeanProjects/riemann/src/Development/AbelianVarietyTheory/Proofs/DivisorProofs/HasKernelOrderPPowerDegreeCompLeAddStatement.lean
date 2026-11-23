import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasKernelOrderPPowerDegreeCompLeAdd
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasKernelOrderPPowerDegree_comp_le_add : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K) (a b c : ℕ), HasLogDeg f a → HasLogDeg g b → HasLogDeg (f ≫ g) c → c ≤ a + b := by
  first | exact @GlobalTheory.Dieu.hasLogDeg_comp_le | exact GlobalTheory.Dieu.hasLogDeg_comp_le | (intros; apply GlobalTheory.Dieu.hasLogDeg_comp_le <;> assumption)
