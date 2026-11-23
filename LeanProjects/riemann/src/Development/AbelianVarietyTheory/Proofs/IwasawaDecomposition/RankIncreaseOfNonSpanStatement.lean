import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RankIncreaseOfNonSpan
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntBilinFormToRealMemBalancedPsdCone
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_increase_of_non_span : ∀ (X : Type) [AddCommGroup X] (m m' : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (ε : Fin m' → LinearMap.BilinForm ℤ X) (w : LinearMap.BilinForm ℤ X), LinearIndependent ℤ δ → (¬ ∃ (M : ℕ) (a : Fin m → ℤ), 0 < M ∧ (M : ℤ) • w = ∑ i, a i • δ i) → (∀ j, ∃ (k : ℕ) (c : Fin m' → ℤ), 0 < k ∧ (k : ℤ) • δ j = ∑ i, c i • ε i) → (∃ (k : ℕ) (c : Fin m' → ℤ), 0 < k ∧ (k : ℤ) • w = ∑ i, c i • ε i) → m < m' := by
  first | exact @GlobalTheory.lt_of_notMem_ratSpan_of_mem_ratSpan | exact GlobalTheory.lt_of_notMem_ratSpan_of_mem_ratSpan | (intros; apply GlobalTheory.lt_of_notMem_ratSpan_of_mem_ratSpan <;> assumption)
