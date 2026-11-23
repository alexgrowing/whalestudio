import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationFunctorial
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.OneSTr
open CrystallineSemistableComparison.Pb.Kap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realization_functorial : ∀ {Λ A B K Λ' A' B' : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] [CommRing Λ'] [CommRing A'] [CommRing B'] (C : Chain.{1} Λ A B K) (C' : Chain.{1} Λ' A' B' K) (h : Hom C C'), C.Good → C'.Good → h.Good → ∀ {j : ℕ} (x : ∀ n, C.S n j) (f : Module.Dual K (C.V j) →+ B), C.Rho x f → C'.Rho (fun n => h.fS n j (x n)) (h.tr j f) := by
  first | exact @GlobalTheory.CompanionTheory.KapRhoHom.rho_hom | exact GlobalTheory.CompanionTheory.KapRhoHom.rho_hom | (intros; apply GlobalTheory.CompanionTheory.KapRhoHom.rho_hom <;> assumption)
