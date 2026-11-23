import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrongApproxClosureMul
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strong_approx_closure_mul : ∀ {F : Type} [Field F] [NumberField F] (d β : F) (s : Pl F), ∀ x ∈ closure (SAQ d β s), ∀ y ∈ closure (SAQ d β s),
  x * y ∈ closure (SAQ d β s) := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.closure_SAQ_mul | exact GlobalTheory.CompanionTheory.PlaneSA.closure_SAQ_mul | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.closure_SAQ_mul <;> assumption)
