import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationAdd
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.OneSTr
open CrystallineSemistableComparison.Pb.Kap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realization_add : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) {j : ℕ} (x y : ∀ n, C.S n j) (f g : Module.Dual K (C.V j) →+ B), C.Rho x f → C.Rho y g → C.Rho (x + y) (f + g) := by
  first | exact @GlobalTheory.CompanionTheory.KapRho.rho_add | exact GlobalTheory.CompanionTheory.KapRho.rho_add | (intros; apply GlobalTheory.CompanionTheory.KapRho.rho_add <;> assumption)
