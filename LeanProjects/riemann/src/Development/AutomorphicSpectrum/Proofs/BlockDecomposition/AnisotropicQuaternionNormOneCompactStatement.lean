import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnisotropicQuaternionNormOneCompact
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.anisotropic_quaternion_norm_one_compact : ∀ {F : Type} [Field F] [NumberField F] (d β : F) (s : Pl F), (∀ x : Q d β (Kp s), qn x = 0 → x = 0) → IsCompact {x : Q d β (Kp s) | qn x = 1} := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.isCompact_qn_eq_one_at_place | exact GlobalTheory.CompanionTheory.PlaneSA.isCompact_qn_eq_one_at_place | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.isCompact_qn_eq_one_at_place <;> assumption)
