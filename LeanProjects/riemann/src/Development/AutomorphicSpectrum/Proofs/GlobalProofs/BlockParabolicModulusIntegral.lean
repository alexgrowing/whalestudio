import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeneralLinearIntegralCompactOpenStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalFieldUniformizerNormPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RelIndexBoxLatticesProduct
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalFieldTopologyNormBalls
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemBoxLatticeIffCongruence
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DiagonalConjugateCongruenceBox
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.ModB

variable {F : Type} [Field F]

def dg {n : ℕ} (v : Fin n → F) (hv : ∀ i, v i ≠ 0) : GL (Fin n) F where
  val := Matrix.diagonal v
  inv := Matrix.diagonal fun i => (v i)⁻¹
  val_inv := by simp [Matrix.diagonal_mul_diagonal, hv]
  inv_val := by simp [Matrix.diagonal_mul_diagonal, hv]

end GlobalTheory.CompanionTheory.QL.ModB
