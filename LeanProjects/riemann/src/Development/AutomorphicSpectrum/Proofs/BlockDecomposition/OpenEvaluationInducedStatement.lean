import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenEvaluationInduced
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecompositionStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_evaluation_induced : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ) (hf : ∀ x ∈ Cl k i t, evX f x = 0),
  ∃ y : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ), (y : smoothPart (ind (HPG k i (t + 1)) (sigO τ σ ψ))).1.1 = eO ψ f := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.MemO.eO_mem | exact GlobalTheory.CompanionTheory.BZPhiPG.MemO.eO_mem | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.MemO.eO_mem <;> assumption)
