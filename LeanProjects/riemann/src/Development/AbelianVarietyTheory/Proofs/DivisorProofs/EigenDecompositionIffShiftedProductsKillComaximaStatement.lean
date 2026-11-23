import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenDecompositionIffShiftedProductsKillComaxima
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatActApply
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenDecomposition_iff_shiftedProducts_kill_comaximal : ∀ (O T V : Type) [CommRing O] [CommRing T] [AddCommGroup V] [Module T V] (ψ : O →+* Module.End T V) (a : ℕ)
  (τ : Fin a → (O →+* T)), (∀ i j, i ≠ j → Ideal.span (Set.range fun x => τ i x - τ j x) = ⊤) → ∀ v : V,
    ((∃ w : Fin a → V, (∀ i, w i ∈ eigSub ψ (τ i)) ∧ v = ∑ i, w i) ↔
      ∀ c : Fin a → O, (List.ofFn fun i => ψ (c i) - algebraMap T (Module.End T V) (τ i (c i))).prod v = 0) := by
  first | (exact @GlobalTheory.UPel.HT.LieLin.decomp_iff_kill) | (exact GlobalTheory.UPel.HT.LieLin.decomp_iff_kill) | (intros; apply GlobalTheory.UPel.HT.LieLin.decomp_iff_kill  <;> assumption)
