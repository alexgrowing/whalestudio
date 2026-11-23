import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.HaarFourierSupport.SuppCongr
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.QuasiOrbits.OrbQ
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.LocallyConstantCosets.FibreQuotientHolds
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.BaseVanishing.VanOf
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.BezoutHypotheses.ContinuousHom

namespace PositivityTheory.RgUd.TP.Nil.Final

open PositivityTheory.RgUd.TP

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nilCore (hT : TraceForm k) (hU : PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k)) : NilCore k :=
  PositivityTheory.RgUd.TP.Nil.Asm.nilCore_of k (PositivityTheory.RgUd.TP.Nil.Four.fourQ k) (PositivityTheory.RgUd.TP.Nil.Orb.orbQ k)
    (PositivityTheory.RgUd.TP.Nil.Fib2.fibQ k) (PositivityTheory.RgUd.TP.Nil.Base.baseQ k) hT hU

end PositivityTheory.RgUd.TP.Nil.Final
