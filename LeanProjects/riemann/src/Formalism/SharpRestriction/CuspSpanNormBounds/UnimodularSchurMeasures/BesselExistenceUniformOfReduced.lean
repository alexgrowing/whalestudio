import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.IdempotentIntegrableOfCoeff
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.TraceConjMulEqHilbertSchmidt
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalL1StatementOfProjectors
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.SmoothVectorsTranslateUnitary

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature

namespace BData

variable (X : BData)

def LowProj : Prop :=
  ∀ P : Mat X.k X.r, IsCayleyU X.k X.r (eps48 X.k X.r) P →
    IsDS (eps48 X.k X.r) (lam48 X.k X.r X.v X.b) (fun g => X.σ (P⁻¹ * g * P)) →
    ∃ E : X.H →L[ℂ] X.H,
      IsOrthProjOnto E (lowKSub (eps48 X.k X.r) (lam48 X.k X.r X.v X.b) (fun g => X.σ (P⁻¹ * g * P)))

def Repro (B : X.H → X.Vp) : Prop :=
  ∀ x ∈ X.G, Integrable (fun g => X.e (Matrix.of g) • X.W' B (x * Matrix.of g)) X.μG ∧
    rconv X.μG X.e (X.W' B) x = X.W' B x

def Exchange (B : X.H → X.Vp) : Prop :=
  ∀ χ, X.IsCut B χ →
    ∫ x, ⟪X.W' B (Matrix.of x), X.Wf B χ (Matrix.of x)⟫_ℂ ∂X.ν =
      ∫ x, ⟪rconv X.μG X.e (X.W' B) (Matrix.of x), X.Φ B χ (Matrix.of x)⟫_ℂ ∂X.ν

variable {X}

end BData

def StepsB2' : Prop :=
  ∀ X : BData, X.Hyp → X.LowSmooth ∧ X.SmoothCyc ∧ X.LowProj ∧
    ∀ B : X.H → X.Vp, X.IsFun B → X.CutStep B ∧ X.ProjectionSquareIntegrable B ∧ X.Repro B ∧ X.Exchange B

def StepsB2'' : Prop :=
  ∀ X : BData, X.Hyp → X.LowSmooth ∧ X.SmoothCyc ∧
    ∀ B : X.H → X.Vp, X.IsFun B → X.CutStep B ∧ X.ProjectionSquareIntegrable B ∧ X.Repro B ∧ X.Exchange B

end Formalism.MainNotions.LeviCoordinates

end
