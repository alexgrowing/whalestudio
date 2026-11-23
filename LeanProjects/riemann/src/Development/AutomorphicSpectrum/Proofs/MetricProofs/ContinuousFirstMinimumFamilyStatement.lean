import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ContinuousFirstMinimumFamily
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_first_minimum_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (X : Type) [TopologicalSpace X] (R : X → RiemLat E g Λ), (∀ v, Continuous fun x => (R x).P v) → (Continuous fun x => (R x).Hm) → Continuous fun x => (R x).lam1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.continuous_first_minimum | exact GlobalTheory.CompanionTheory.Ar.Cusp.continuous_first_minimum | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.continuous_first_minimum <;> assumption)
