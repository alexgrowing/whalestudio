import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesExistsUniqueDecompOverFrobeniusLikeEn
open scoped PowerSeries Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo : ∀ {O : Type} [CommRing O] (l : ℕ), 2 ≤ l → ∀ (φ : O⟦X⟧ →ₐ[O] O⟦X⟧), (∀ (f : O⟦X⟧) (m : ℕ), PowerSeries.coeff m (φ f) = if l ∣ m then PowerSeries.coeff (m / l) f else 0) → ∀ f : O⟦X⟧, ∃! g : Fin l → O⟦X⟧, f = ∑ j : Fin l, PowerSeries.X ^ j.val * φ (g j) := by
  first | exact @GlobalTheory.InertiaEigenvalues.PowerSeriesFree.main | exact GlobalTheory.InertiaEigenvalues.PowerSeriesFree.main | (intros; apply GlobalTheory.InertiaEigenvalues.PowerSeriesFree.main <;> assumption)
