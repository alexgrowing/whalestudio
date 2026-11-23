import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankProductLeOne
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorProductRankLeOneStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_rank_product_le_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (h N : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), Module.rank ℂ (TwJacquet (prodIrr x hd) (unipB k (Fin N)) (whitChar ψ N)) ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.RgGu.rank_twJacquet_prodIrr_le_one | exact GlobalTheory.CompanionTheory.RgGu.rank_twJacquet_prodIrr_le_one | (intros; apply GlobalTheory.CompanionTheory.RgGu.rank_twJacquet_prodIrr_le_one <;> assumption)
