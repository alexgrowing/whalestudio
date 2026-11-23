import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogIndexOfOrthogonalFamily
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsAdapted
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_index_of_orthogonal_family : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (r : ℕ) (v : Fin r → V), 2 * Fintype.card Ψ = Module.finrank ℚ E → IsOFamily A.ρ A.I v → ∀ s, logIdx (A.tor s) (fun a => eigComp A.ρ (A.σ s) (v a)) / Module.finrank ℚ L = -(r * Real.log (|(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ)))) + Real.log (((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) / Module.finrank ℚ E := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.torusPartDegree | exact GlobalTheory.CompanionTheory.Ar.Cusp.torusPartDegree | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.torusPartDegree <;> assumption)
