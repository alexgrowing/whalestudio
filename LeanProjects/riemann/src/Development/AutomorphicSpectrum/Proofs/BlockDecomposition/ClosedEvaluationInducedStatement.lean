import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedEvaluationInduced
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecompositionStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_evaluation_induced : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ),
  ∃ y : cIndSpace (MirabolicParabolic k (i + 1) t) (sigC τ σ), (y : smoothPart (ind (MirabolicParabolic k (i + 1) t) (sigC τ σ))).1.1 = eC ψ f := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.MemC.memC | exact GlobalTheory.CompanionTheory.BZPhiPG.MemC.memC | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.MemC.memC <;> assumption)
