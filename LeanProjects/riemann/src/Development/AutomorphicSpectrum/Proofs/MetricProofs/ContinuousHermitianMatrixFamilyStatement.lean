import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ContinuousHermitianMatrixFamily
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_hermitian_matrix_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (X : Type) [TopologicalSpace X] (R : X → RiemLat E g Λ) (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ), (∀ x, (R x).form = form) → (∀ v, Continuous fun x => (R x).P v) → Continuous fun x => (R x).Hm := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.continuous_Hm | exact GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.continuous_Hm | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.continuous_Hm <;> assumption)
