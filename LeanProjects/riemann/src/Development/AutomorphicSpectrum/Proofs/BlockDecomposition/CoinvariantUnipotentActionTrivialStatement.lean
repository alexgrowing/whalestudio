import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinvariantUnipotentActionTrivial
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coinvariant_unipotent_action_trivial : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (u : HPG k (i + 1) (t + 1)) (h1 : (pgProj k (i + 1) (t + 1) u).1 ∈ MirUin k (i + 1)) (h2 : (pgProj k (i + 1) (t + 1) u).2 = 1) (w : τ.V ⊗[ℂ] σ.V), qC τ σ (sigX τ σ u w) = qC τ σ w := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.qC_sigX_unip | exact GlobalTheory.CompanionTheory.BZPhiPG.qC_sigX_unip | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.qC_sigX_unip <;> assumption)
