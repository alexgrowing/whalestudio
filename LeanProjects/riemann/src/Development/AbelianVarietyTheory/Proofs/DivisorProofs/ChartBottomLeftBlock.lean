import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.DotAddRight
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ModeHalfStatementPfA

noncomputable section

namespace GlobalTheory.ChartGraph

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def chartMatrixTopBlock (X : Data E r) (z : V (nd X)) (τ : X.Ψ) : Matrix (Fin X.p0) (Fin X.p0) ℂ :=
  (mat (nmat X z) τ).submatrix (Fin.castLE X.p0_le) (Fin.castLE X.p0_le)

def chartBottomLeftBlock (X : Data E r) (z : V (nd X)) (τ : X.Ψ) : Matrix (Fin (r - X.p0)) (Fin X.p0) ℂ :=
  (mat (nmat X z) τ).submatrix (fun m => ⟨X.p0 + m, by have := m.isLt; have := X.p0_le; omega⟩)
    (Fin.castLE X.p0_le)

def graphCoord (X : Data E r) (z : V (nd X)) : X.Coord := fun τ => chartBottomLeftBlock X z τ * (chartMatrixTopBlock X z τ)⁻¹

end GlobalTheory.ChartGraph
