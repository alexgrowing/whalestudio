import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorFixedNearIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulMemBall
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_vector_fixed_near_identity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (w : τ.V ⊗[ℂ] σ.V),
  ∃ O ∈ nhds (1 : Mir k ((i + 1) + t + 1)), ∀ h : HPG k (i + 1) (t + 1), ((h : Mir k ((i + 1) + (t + 1))) ∈ O) → sigX τ σ h w = w := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Onto.sigX_fix | exact GlobalTheory.CompanionTheory.BZPhiPG.Onto.sigX_fix | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Onto.sigX_fix <;> assumption)
