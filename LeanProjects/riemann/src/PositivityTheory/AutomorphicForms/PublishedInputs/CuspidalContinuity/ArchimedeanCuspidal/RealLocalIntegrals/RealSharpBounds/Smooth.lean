import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealSharpBounds.Bounds
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealTemperedBounds.CrdTemperate

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace Ad3.LR.B

def clS (l j : Fin 3) : M3 →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => Fin 3 → ℝ) l))

def ellS (i j : Fin 3) (m : M3) : M3 →L[ℝ] ℂ := ∑ l, ((Matrix.of m)⁻¹ i l) • clS l j

abbrev U3 : Set M3 := {m | (Matrix.of m).det ≠ 0}

end Ad3.LR.B
