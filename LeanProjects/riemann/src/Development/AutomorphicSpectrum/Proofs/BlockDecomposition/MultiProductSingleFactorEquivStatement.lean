import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiProductSingleFactorEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClOfSelf
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M GlobalTheory.CompanionTheory.WordProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multi_product_single_factor_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a : IrrGL k) {α : Type} [Fintype α] [LinearOrder α] (b : α → ℕ) (i₀ : α), b i₀ = a.1 → (∀ i, i ≠ i₀ → b i = 0) → ∀ (g : (Σ i, Fin (b i)) ≃ Fin a.1), Nonempty ((multiProd g fun i => (clOf a (b i)).rep.ρ).Equiv a.rep) := by
  first | exact @GlobalTheory.CompanionTheory.WordProd.OneBlockProd.multiProd_clOf_single | exact GlobalTheory.CompanionTheory.WordProd.OneBlockProd.multiProd_clOf_single | (intros; apply GlobalTheory.CompanionTheory.WordProd.OneBlockProd.multiProd_clOf_single <;> assumption)
