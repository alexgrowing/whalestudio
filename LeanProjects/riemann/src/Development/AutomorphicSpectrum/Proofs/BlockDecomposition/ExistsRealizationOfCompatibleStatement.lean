import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRealizationOfCompatible
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.OneSTr
open CrystallineSemistableComparison.Pb.Kap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realization_of_compatible : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) (hC : C.Good) {j : ℕ} (x : ∀ n, C.S n j), C.Comp x → ∃ f : Module.Dual K (C.V j) →+ B, C.Rho x f := by
  first | exact @GlobalTheory.CompanionTheory.KapRho.exists_rho | exact GlobalTheory.CompanionTheory.KapRho.exists_rho | (intros; apply GlobalTheory.CompanionTheory.KapRho.exists_rho <;> assumption)
