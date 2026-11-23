import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDomainClosedDiscGaugeCompletionOfEquivNorm
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDomain_closedDiscGaugeCompletion_of_equiv_norm : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (u : A) (ρ : ℝ≥0), ∀ (N : A → ℝ) (c : ℝ), 0 < c → (∀ x y, N (x * y) = N x * N y) → (∀ x y, N (x + y) ≤ max (N x) (N y)) → N (l : A) = (l : ℝ)⁻¹ → (∀ x, N x ≤ ‖toDisc l u ρ x‖) → (∀ x, c * ‖toDisc l u ρ x‖ ≤ N x) → IsDomain (Disc l u ρ) ∧ ∀ x y : Disc l u ρ, c ^ 2 * (‖x‖ * ‖y‖) ≤ ‖x * y‖ := by
  first | exact @GlobalTheory.BSP.DiscDomain.isDomain_disc | exact GlobalTheory.BSP.DiscDomain.isDomain_disc | (intros; apply GlobalTheory.BSP.DiscDomain.isDomain_disc <;> assumption)
