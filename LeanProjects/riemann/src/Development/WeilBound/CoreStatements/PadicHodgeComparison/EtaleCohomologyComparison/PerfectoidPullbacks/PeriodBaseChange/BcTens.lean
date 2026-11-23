import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothModelTensorWittComparisonStatement
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PeriodBaseChange.BWMorL

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg

namespace CrystallineSemistableComparison.Pb

theorem bc_tens : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K), M.Sm →
    ∀ j n, Tens (WittVector l r.k) (N := fun _ : Unit => AW r) (M := fun _ => (HSW r M j).M n) (M' := Mid.HM r M n j)
      fun _ a y => idA r a • bW r M n j y := fun r M hM j n => GlobalTheory.T.smooth_model_tensor_witt_comparison r M hM j n

end CrystallineSemistableComparison.Pb
