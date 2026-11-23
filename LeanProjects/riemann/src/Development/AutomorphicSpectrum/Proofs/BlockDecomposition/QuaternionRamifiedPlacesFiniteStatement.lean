import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionRamifiedPlacesFinite
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_ramified_places_finite : ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ r : F, r ^ 2 ≠ d) → β ≠ 0 →
  {u : Pl F | ∀ x : Q d β (Kp u), qn x = 0 → x = 0}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.finite_anisotropic_places | exact GlobalTheory.CompanionTheory.PlaneSA.finite_anisotropic_places | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.finite_anisotropic_places <;> assumption)
