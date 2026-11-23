import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothModelTensorWittComparison
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PeriodBaseChange.BWMorL
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_model_tensor_witt_comparison : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K), M.Sm → ∀ j n, Tens (WittVector l r.k) (N := fun _ : Unit => AW r) (M := fun _ => (Wc.HS l (B.schFn M.p) r.ρ j).M n) (M' := Mid.HM r M n j) fun _ a y => idA r a • bWL r M n j y := by
  first | exact @GlobalTheory.CompanionTheory.BcAcris.bc_tens | exact GlobalTheory.CompanionTheory.BcAcris.bc_tens | (intros; apply GlobalTheory.CompanionTheory.BcAcris.bc_tens <;> assumption)
