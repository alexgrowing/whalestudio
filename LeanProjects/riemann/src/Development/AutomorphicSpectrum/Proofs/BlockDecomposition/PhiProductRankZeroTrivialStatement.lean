import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiProductRankZeroTrivial
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_product_rank_zero_trivial : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (ρ : GRep k (m + 1)) (τ : MRep k 0) (h : (m + 1) + 0 = (m + 0) + 1), IsSmooth ρ.ρ → IsSmooth τ.ρ → Subsingleton (phiN ψ (mcast h (prodGPn ρ τ))).V := by
  first | exact @GlobalTheory.CompanionTheory.PhiGpZero.phiN_prodGPn_zero | exact GlobalTheory.CompanionTheory.PhiGpZero.phiN_prodGPn_zero | (intros; apply GlobalTheory.CompanionTheory.PhiGpZero.phiN_prodGPn_zero <;> assumption)
