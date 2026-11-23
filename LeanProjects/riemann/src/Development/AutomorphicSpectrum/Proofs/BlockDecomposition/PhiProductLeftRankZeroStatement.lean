import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiProductLeftRankZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_product_left_rank_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (i : ℕ) (τ : MRep k (i + 1)) (σ : GRep k 0) (h : (i + 1) + 0 = (i + 0) + 1), IsSmooth τ.ρ → IsSmooth σ.ρ → MIso (phiN ψ (mcast h (prodPGn τ σ))) (prodPGn (phiN ψ τ) σ) := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.GLZero.phiN_prodPGn_zero | exact GlobalTheory.CompanionTheory.LeibOrd.GLZero.phiN_prodPGn_zero | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.GLZero.phiN_prodPGn_zero <;> assumption)
