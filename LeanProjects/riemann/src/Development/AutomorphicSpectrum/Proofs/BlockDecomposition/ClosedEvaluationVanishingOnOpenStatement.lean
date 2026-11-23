import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedEvaluationVanishingOnOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecompositionStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_evaluation_vanishing_on_open : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ) (hf : ∀ x ∈ Cl k i t, evX f x = 0),
  eC ψ f = 0 := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.eC_eq_zero_of_vanish | exact GlobalTheory.CompanionTheory.BZPhiPG.eC_eq_zero_of_vanish | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.eC_eq_zero_of_vanish <;> assumption)
