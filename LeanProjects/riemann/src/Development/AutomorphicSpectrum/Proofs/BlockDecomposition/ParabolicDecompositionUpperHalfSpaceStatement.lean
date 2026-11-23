import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicDecompositionUpperHalfSpace
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_decomposition_upper_half_space : ∀ (n : ℕ) (p : PositivityTheory.Rg.Sw.GR n), (PositivityTheory.Rg.Sw.mR p).toBlocks₂₁ = 0 → ∃ (nb ma : PositivityTheory.Rg.Sw.GR n) (b a : Matrix (Fin n) (Fin n) ℂ), bᴴ = b ∧ IsUnit a.det ∧ PositivityTheory.Rg.Sw.mR nb = PositivityTheory.Rg.Sw.nU b ∧ PositivityTheory.Rg.Sw.mR ma = Matrix.fromBlocks a 0 0 (aᴴ)⁻¹ ∧ p = nb * ma ∧ ((PositivityTheory.Rg.Sw.mR p).toBlocks₁₁ * (Complex.I • 1) + (PositivityTheory.Rg.Sw.mR p).toBlocks₁₂) * ((PositivityTheory.Rg.Sw.mR p).toBlocks₂₁ * (Complex.I • 1) + (PositivityTheory.Rg.Sw.mR p).toBlocks₂₂)⁻¹ = b + Complex.I • (a * aᴴ) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelPoint.siegel_point | exact GlobalTheory.CompanionTheory.SiegelPoint.siegel_point | (intros; apply GlobalTheory.CompanionTheory.SiegelPoint.siegel_point <;> assumption)
