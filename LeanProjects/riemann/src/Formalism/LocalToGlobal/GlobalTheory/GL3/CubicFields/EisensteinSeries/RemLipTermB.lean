import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EisensteinSeries.RemLipTermA

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.RLT

open MeasureTheory

def maj (y b t : ℝ) (a : ℝ) (s : ℝ) : ℝ := (s - 1) * (2 * Real.exp |Real.log y| * y) *
  ((1 + 2 * |Real.log y| + 4 * |Real.log b|) * qv a b t ^ (-(3 / 2) : ℝ) + 4 / b * qv a b t ^ (-1 : ℝ))

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.RLT
