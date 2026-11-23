import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.SPrimeOf
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsBound
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GBClose
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.IntegrableOfBound
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Integr
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsGainA

namespace PositivityTheory.Rg.Sw.SP

theorem sPrime_of : SPrimeOf :=
  sPrime_of' PositivityTheory.Rg.Sw.WR.B.clsBound PositivityTheory.Rg.Sw.WR.K.GB.clsGainB PositivityTheory.Rg.Sw.WR.ibp PositivityTheory.Rg.Sw.WR.I.integr
    PositivityTheory.Rg.Sw.WR.Z.chain PositivityTheory.Rg.Sw.WR.Z.ext

end PositivityTheory.Rg.Sw.SP
