import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationSmul
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.OneSTr
open CrystallineSemistableComparison.Pb.Kap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realization_smul : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) {j : ℕ} (c : Λ) (x : ∀ n, C.S n j) (f : Module.Dual K (C.V j) →+ B), C.Rho x f → C.Rho (c • x) ((AddMonoidHom.mulLeft (C.ι (C.lam c))).comp f) := by
  first | exact @GlobalTheory.CompanionTheory.KapChain.rho_smul | exact GlobalTheory.CompanionTheory.KapChain.rho_smul | (intros; apply GlobalTheory.CompanionTheory.KapChain.rho_smul <;> assumption)
