import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransposeInvariantOfConjInvariantDistributionGL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transpose_invariant_of_conj_invariant_distribution_GL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (T : SB (GL n k) →ₗ[ℂ] ℂ), (∀ (g : GL n k) (φ ψ : SB (GL n k)), (∀ x, ψ.1 x = φ.1 (g * x * g⁻¹)) → T ψ = T φ) → ∀ φ ψ : SB (GL n k), (∀ x y : GL n k, y.val = x.val.transpose → ψ.1 x = φ.1 y) → T ψ = T φ := by
  first | exact @GlobalTheory.GelfandKazhdan.transpose_invariant | exact GlobalTheory.GelfandKazhdan.transpose_invariant | (intros; apply GlobalTheory.GelfandKazhdan.transpose_invariant <;> assumption)
