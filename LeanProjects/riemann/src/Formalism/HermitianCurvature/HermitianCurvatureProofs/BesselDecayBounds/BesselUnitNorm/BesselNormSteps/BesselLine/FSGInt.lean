import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.FSFInt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.FSFdeg

open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.FSW

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

section Lemmas

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]

def trL : (Wp →L[ℂ] Wp) →L[ℂ] ℂ :=
  ∑ i, (innerSL ℂ (stdOrthonormalBasis ℂ Wp i)).comp (ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wp i))

def kap (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (p : Mt k r × Mt k r) : ℂ :=
  psi k r z c (Matrix.of p.2) * star (trW (π (Matrix.of p.1)⁻¹))

end Lemmas

end PI.WBL.FSW
