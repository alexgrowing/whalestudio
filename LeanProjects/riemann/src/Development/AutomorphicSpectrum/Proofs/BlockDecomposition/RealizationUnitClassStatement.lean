import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationUnitClass
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.OneSTr
open CrystallineSemistableComparison.Pb.Kap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realization_unit_class : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) (hC : C.Good) (P : Cup C), P.Good → ∀ h : Module.Dual K (C.V 0) →+ B, C.Rho P.oneS h → ∀ φ : Module.Dual K (C.V 0), h φ = C.o (φ P.oneV) := by
  first | exact @GlobalTheory.CompanionTheory.KapUnit.rho_one_eval | exact GlobalTheory.CompanionTheory.KapUnit.rho_one_eval | (intros; apply GlobalTheory.CompanionTheory.KapUnit.rho_one_eval <;> assumption)
