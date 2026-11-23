import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeakApproximationIntegral
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weak_approximation_integral : ∀ {F : Type} [Field F] [NumberField F] (s : Pl F) (T : Finset (Pl F)), s ∉ T →
  ∀ O : (u : Pl F) → Set (Kp u), (∀ u ∈ T, IsOpen (O u) ∧ (O u).Nonempty) →
  ∃ t : F, (∀ u ∈ T, algebraMap F (Kp u) t ∈ O u) ∧
    ∀ v : HeightOneSpectrum (𝓞 F), (Sum.inr v : Pl F) ∉ T → (Sum.inr v : Pl F) ≠ s →
      algebraMap F (Kp (Sum.inr v : Pl F)) t ∈ Ov v := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.additive_strong_approx_away | exact GlobalTheory.CompanionTheory.PlaneSA.additive_strong_approx_away | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.additive_strong_approx_away <;> assumption)
