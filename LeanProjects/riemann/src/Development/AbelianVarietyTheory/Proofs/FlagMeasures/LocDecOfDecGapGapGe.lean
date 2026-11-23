import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem locDec_of_decGap_gapGe : DecGap → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → GapGe B h →
    (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h := by
  intro hD B d h hds hgap hh v g
  obtain ⟨h1, h2, h3, -⟩ := hds v
  have hw : B.w v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v) := h3.2
  have hn : ‖B.w v‖ = 1 := h3.1
  have := (hD _ _ _ _ _ h1 h2 h (hgap v) (hh v) (uMat g) g.2 _ hw _ hw).2
  simpa [hn] using this

end GlobalTheory.Dec
