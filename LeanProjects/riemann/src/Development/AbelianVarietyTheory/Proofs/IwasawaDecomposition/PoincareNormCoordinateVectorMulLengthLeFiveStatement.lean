import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PoincareNormCoordinateVectorMulLengthLeFive
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
open Matrix
open scoped ComplexOrder Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareNorm_coordinateVector_mul_length_le_five : ∀ (n a : ℕ) (ha : a ≤ n) (ρ : ℝ), ρ ≤ 1 / 2 → ∀ v : ReciprocityTheory.L2DbarEstimates.V n, v.ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ → ∀ k : Fin n, GlobalTheory.HermFrame.gnorm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.poincareGram a v.ofLp) (Pi.single k 1) * GlobalTheory.GoodMetric.poinWt (Finset.univ.map (Fin.castLEEmb ha)) v k ≤ 5 := by
  first | exact @GlobalTheory.PoinLen.gnorm_mul_poinWt_le_five | exact GlobalTheory.PoinLen.gnorm_mul_poinWt_le_five | (intros; apply GlobalTheory.PoinLen.gnorm_mul_poinWt_le_five <;> assumption)
