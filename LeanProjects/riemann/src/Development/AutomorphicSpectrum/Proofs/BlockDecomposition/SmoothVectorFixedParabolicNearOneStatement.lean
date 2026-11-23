import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorFixedParabolicNearOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBump
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_vector_fixed_parabolic_near_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ)
    (v : τ.V ⊗[ℂ] σ.V), ∃ O ∈ 𝓝 (1 : Mir k ((i + 1) + t + 1)), ∀ a : HPG k (i + 1) (t + 1),
      (a : Mir k ((i + 1) + (t + 1))) ∈ O → sigX τ σ a v = v := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.sigX_fix_nhds | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.sigX_fix_nhds | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.sigX_fix_nhds <;> assumption)
