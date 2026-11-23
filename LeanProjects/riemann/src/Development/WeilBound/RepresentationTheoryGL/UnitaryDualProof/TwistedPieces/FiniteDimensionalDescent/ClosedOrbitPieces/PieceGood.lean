import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.RootsFinite
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.TwFin
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.IsClosedRank
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.RatioOf
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.Transfer
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.FrobeniusReciprocity.FrobProof

namespace PositivityTheory.RgUd.TP.Desc.Piece.Final

open PositivityTheory.RgUd.TP.Desc

theorem pieceGood (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PieceGood k :=
  PositivityTheory.RgUd.TP.Desc.Piece.PAsm2.pieceGood_of k PositivityTheory.PfBern.Frob.frobeniusReciprocity (PositivityTheory.RgUd.TP.Desc.Piece.PSect.sect k)
    (PositivityTheory.RgUd.TP.Desc.Piece.PTop.pieceTop k) (PositivityTheory.RgUd.TP.Desc.Piece.PDich.dich k)
    (PositivityTheory.RgUd.TP.Desc.Piece.PTr.transfer k)

end PositivityTheory.RgUd.TP.Desc.Piece.Final
