import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame

section
noncomputable section
open Matrix Topology Filter
open scoped ContDiff
namespace GlobalTheory.BesselMapOne
section Smooth
open Formalism.MainNotions.S Formalism.L2.Theta Formalism.QuantumDeterminants GlobalTheory.SmVec
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {J : Matrix (Fin n) (Fin n) ℂ}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
end
end Smooth
section Frame
open PI.UpqRep PI.HwUniqW GlobalTheory.RealBessel
variable {k r : ℕ}
variable {z : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
end Frame
section Dual
open PI.UpqRep PI.HwUniqW GlobalTheory.RealBessel
variable {k : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
end Dual
section Main
open PI.UpqRep PI.HwUniqW GlobalTheory.RealBessel PI.BesselMapUniq GlobalTheory.SmVec
variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
end Main
end GlobalTheory.BesselMapOne
end
end
