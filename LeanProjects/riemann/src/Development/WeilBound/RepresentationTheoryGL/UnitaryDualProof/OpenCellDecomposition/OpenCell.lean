import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.OpenCell
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.PiTensorNontriviality.ExpLow

namespace PositivityTheory.RgUd.Cell

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem openCell : PositivityTheory.RgUd.OpenCell k := PositivityTheory.RgUd.CellA.openCell k

theorem expLow : PositivityTheory.RgUd.BesselSum k → PositivityTheory.RgUd.OpenCell k → PositivityTheory.RgUd.ExpLow k := PositivityTheory.RgUd.CellE.expLow k

end PositivityTheory.RgUd.Cell
