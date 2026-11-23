import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.SPrimeOfAlt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.Bridge
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.CayDiv
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.DerivationConstantVanishes
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.DetEqZeroOfRankLt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.MinorZ
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.SecOneConst

namespace PositivityTheory.Rg.Sw.SP

theorem sPrime_of_minor (h : MinorFormula) : SPrime :=
  sPrime_of bridge (cayDiv_of comm (minorZ_of h) (minorZ'_of h) null)

theorem wrOrd_of_minor (h : MinorFormula) : PositivityTheory.SiegelWeilFormula.Gen.WROrd := wrOrd_of (sPrime_of_minor h)

end PositivityTheory.Rg.Sw.SP
