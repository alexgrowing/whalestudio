import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewtonApproximationLocalToGlobal
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newton_approximation_local_to_global : ∀ {S : Type} [CommRing S] (ϖ : S), (∀ m : Ideal S, m.IsMaximal → Step (Ideal.Quotient.mk (compI m) ϖ)) → Step ϖ := by
  first | exact @GlobalTheory.CompanionTheory.NewtonStep.step_of_forall_maximal | exact GlobalTheory.CompanionTheory.NewtonStep.step_of_forall_maximal | (intros; apply GlobalTheory.CompanionTheory.NewtonStep.step_of_forall_maximal <;> assumption)
