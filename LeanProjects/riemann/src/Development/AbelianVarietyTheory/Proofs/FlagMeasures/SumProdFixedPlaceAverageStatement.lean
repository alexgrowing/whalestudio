import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumProdFixedPlaceAverage
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_prod_fixed_place_average_alt : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)] [∀ i, DecidableEq (G i)] {V : Type} [AddCommGroup V] [Module ℂ V] (a : ∀ i, G i → ℂ) (f : (∀ i, G i) → V), (∀ i (γ : ∀ i, G i), γ i = 1 → ∑ β : G i, a i β • f (Function.update γ i β) = f γ) → ∑ γ : (∀ i, G i), (∏ i, a i (γ i)) • f γ = f 1 := by
  first | exact @GlobalTheory.sum_prod_fixed_place_average | exact GlobalTheory.sum_prod_fixed_place_average | (intros; apply GlobalTheory.sum_prod_fixed_place_average <;> assumption)
