import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.EquivariantCalculus.Equi

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace PositivityTheory.RgBcC.Calc2.L

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Calc2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def co (Y : Mat n) (p : Bool × Fin n × Fin n) : ℝ := if p.1 then (Y p.2.1 p.2.2).re else (Y p.2.1 p.2.2).im

end PositivityTheory.RgBcC.Calc2.L
