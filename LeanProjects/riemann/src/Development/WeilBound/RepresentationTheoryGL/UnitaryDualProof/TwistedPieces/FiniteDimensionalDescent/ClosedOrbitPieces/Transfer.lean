import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.DoubleTransfer
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.OrbClosed
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.TransferOf

namespace PositivityTheory.RgUd.TP.Desc.Piece.PTr

open PositivityTheory.RgUd.TP.Desc.Piece

theorem transfer (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Transfer k :=
  TrI.transfer_of k TrDbl.doubleTransfer (TrOrb.orbHom k) (TrOrb.orbClosed k)

end PositivityTheory.RgUd.TP.Desc.Piece.PTr
