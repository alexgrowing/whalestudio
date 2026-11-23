import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscTopologicalBasisExpansion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedDisc_topologicalBasis_expansion : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type) (TB : TopBasis s bk.J ι) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ j : bk.DS ρ →+* Disc l (s X) ρ, IsDiscMap s j → ∀ cD : ι → (Disc l (s X) ρ →+ bk.DS ρ), ((∀ i a, cD i (toDisc l (s X) ρ a) = toDisc l (X : bk.S) ρ (TB.c i a)) ∧ (∀ i x y, cD i (j x * y) = x * cD i y) ∧ (∀ i y, ‖cD i y‖ ≤ ‖y‖)) → ∀ y, Filter.Tendsto (fun i => cD i y) Filter.cofinite (nhds 0) ∧ HasSum (fun i => j (cD i y) * toDisc l (s X) ρ (TB.b i)) y := by
  first | exact @GlobalTheory.BSP.DiscExpand.disc_expand | exact GlobalTheory.BSP.DiscExpand.disc_expand | (intros; apply GlobalTheory.BSP.DiscExpand.disc_expand <;> assumption)
