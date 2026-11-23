import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimProductTranslates
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
open Matrix GlobalTheory.TorFin
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_dim_product_translates : ∀ (G ι : Type) [Group G] (T : ι → Set G) (c : G → ℂ), (∀ i j, i ≠ j → ∀ a ∈ T i, ∀ b ∈ T j, a * b = b * a) → (∀ i, FiniteDimensional ℂ (Submodule.span ℂ {f : G → ℂ | ∃ a ∈ T i, f = fun g => c (a * g)})) → ∀ l : List ι, l.Nodup → FiniteDimensional ℂ (Submodule.span ℂ {f : G → ℂ | ∃ a : ι → G, (∀ i, a i ∈ T i) ∧ f = fun g => c ((l.map a).prod * g)}) := by
  first | exact @GlobalTheory.TorFin.Comb.finiteDimensional_span_translates_prod | exact GlobalTheory.TorFin.Comb.finiteDimensional_span_translates_prod | (intros; apply GlobalTheory.TorFin.Comb.finiteDimensional_span_translates_prod <;> assumption)
