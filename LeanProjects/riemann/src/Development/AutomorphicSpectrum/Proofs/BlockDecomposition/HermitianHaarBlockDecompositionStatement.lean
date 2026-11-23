import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianHaarBlockDecomposition
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousBlkM
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_haar_block_decomposition : ∀ (n : ℕ) (ν : Measure (hermC (n + 1))) (ν' : Measure (hermC n)),
    ν.IsAddHaarMeasure → ν'.IsAddHaarMeasure →
    ∃ c : ENNReal, c ≠ ⊤ ∧ ∀ F : hermC (n + 1) → ENNReal, Measurable F →
      ∫⁻ b, F b ∂ν = c * ∫⁻ b', ∫⁻ u : Fin n → ℂ, ∫⁻ d : ℝ, F (blk b' u d) ∂volume ∂volume ∂ν' := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.haar_blocks | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.haar_blocks | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.haar_blocks <;> assumption)
