import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients

open MeasureTheory NumberField Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace

namespace GlobalTheory.Dec

theorem locDec_of_decOp (hD : DecOp) (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ) (hB : IsDSData B d)
    (hg : GapGe B h) (hh : ∀ v, 8 * (B.I.n : ℝ) * rkR (B.I.ε v) < h) : LocDec B h := by
  intro v g
  obtain ⟨h1, h2, h3, -⟩ := hB v
  simpa [h3.1] using hD _ _ _ _ _ h1 h2 h (hg v) (hh v) (uMat g) g.2 _ h3.2 _ h3.2

theorem locDec_of_decGap (hD : GlobalTheory.DSId.DecGap) (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ)
    (hB : IsDSData B d) (hg : GapGe B h)
    (hh : ∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) : LocDec B h := by
  intro v g
  obtain ⟨h1, h2, h3, -⟩ := hB v
  simpa [h3.1] using (hD _ _ _ _ _ h1 h2 h (hg v) (hh v) (uMat g) g.2 _ h3.2 _ h3.2).2

end GlobalTheory.Dec
