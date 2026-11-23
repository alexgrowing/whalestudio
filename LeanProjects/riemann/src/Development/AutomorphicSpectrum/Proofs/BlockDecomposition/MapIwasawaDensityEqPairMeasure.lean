import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Sec2
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableUR

noncomputable section

open MeasureTheory Matrix Complex
open Ad3 Ad3.LR Ad3.K.GL2LocalData Ad3.K.GL2LocalData.WR GlobalTheory.CompanionTheory.GL2LocalData.RealWhittakerFirst GlobalTheory.CompanionTheory.TateR

namespace GlobalTheory.CompanionTheory.GL2LocalData.RealWhittakerFirst.Push

def ray (G : (Fin 2 → ℝ) → ENNReal) (x : ℝ) : ENNReal :=
  ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r * G ![r * Real.cos x, r * Real.sin x]

end GlobalTheory.CompanionTheory.GL2LocalData.RealWhittakerFirst.Push

end
