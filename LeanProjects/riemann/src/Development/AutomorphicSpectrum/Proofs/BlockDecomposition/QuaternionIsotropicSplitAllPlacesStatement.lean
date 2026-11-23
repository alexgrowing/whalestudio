import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionIsotropicSplitAllPlaces
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeakApproximationIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrongApproxClosureMulStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportProductOverPlacesStatement
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_isotropic_split_all_places : ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ r : F, r ^ 2 ≠ d) → β ≠ 0 →
  (∃ x : Q d β F, x ≠ 0 ∧ qn x = 0) → ∀ s : Pl F, QSA d β s := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.Split.strong_approx_split | exact GlobalTheory.CompanionTheory.PlaneSA.Split.strong_approx_split | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.Split.strong_approx_split <;> assumption)
