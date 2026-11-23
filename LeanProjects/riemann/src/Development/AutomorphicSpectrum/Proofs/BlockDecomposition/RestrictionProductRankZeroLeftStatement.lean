import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionProductRankZeroLeft
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restriction_product_rank_zero_left : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (j n : ℕ) (π₁ : GRep k 0) (π₂ : GRep k (j + 1)) (h : 0 + (j + 1) = n + 1) (h' : 0 + j = n), IsSmooth π₁.ρ → IsSmooth π₂.ρ → MIso (gres ((π₁.prod π₂).cast h)) (mcast h' (prodGPn π₁ (gres π₂))) := by
  first | exact @GlobalTheory.CompanionTheory.LeibRes0Left.gres_prod_zero_left' | exact GlobalTheory.CompanionTheory.LeibRes0Left.gres_prod_zero_left' | (intros; apply GlobalTheory.CompanionTheory.LeibRes0Left.gres_prod_zero_left' <;> assumption)
