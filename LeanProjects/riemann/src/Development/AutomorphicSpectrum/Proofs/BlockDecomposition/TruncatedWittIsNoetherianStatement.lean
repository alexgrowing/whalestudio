import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedWittIsNoetherian
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncated_witt_isNoetherian : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l], IsNoetherianRing (Wc.Wm l k 1) := by
  first | exact @GlobalTheory.CompanionTheory.WittLevel.isNoetherianRing_Wm_one | exact GlobalTheory.CompanionTheory.WittLevel.isNoetherianRing_Wm_one | (intros; apply GlobalTheory.CompanionTheory.WittLevel.isNoetherianRing_Wm_one <;> assumption)
