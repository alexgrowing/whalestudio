import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.ConeHaar

open PositivityTheory.RgBcC

def coneW (n : ℕ) (v : Fin n × Fin n → ℝ) : ℝ≥0∞ := ENNReal.ofReal (((hOf v).det.re ^ n)⁻¹)

def coneMeas (n : ℕ) : Measure (Fin n × Fin n → ℝ) :=
  (volume.restrict (cone n)).withDensity (coneW n)

end GlobalTheory.CompanionTheory.ConeHaar
