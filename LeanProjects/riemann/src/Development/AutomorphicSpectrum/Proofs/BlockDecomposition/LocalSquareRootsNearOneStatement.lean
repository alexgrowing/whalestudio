import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSquareRootsNearOne
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_square_roots_near_one : ∀ {F : Type} [Field F] [NumberField F] (u : Pl F), ∀ V ∈ 𝓝 (1 : Kp u), ∀ᶠ x in 𝓝 (1 : Kp u), ∃ μ ∈ V, μ ^ 2 = x := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.sq_fills_nhds_one | exact GlobalTheory.CompanionTheory.PlaneSA.sq_fills_nhds_one | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.sq_fills_nhds_one <;> assumption)
