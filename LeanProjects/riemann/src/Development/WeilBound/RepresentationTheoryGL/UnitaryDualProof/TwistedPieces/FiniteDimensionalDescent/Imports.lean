import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.DescOf
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.RestrL
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.PieceGood

namespace PositivityTheory.RgUd.TP.Desc.Final

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem desc (p : ℕ) [Fact p.Prime] [CharP k p] (hU : PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k)) : Desc k :=
  Asm.desc_of k (Restr.Final.restr k) (Piece.Final.pieceGood k) p hU

end PositivityTheory.RgUd.TP.Desc.Final
