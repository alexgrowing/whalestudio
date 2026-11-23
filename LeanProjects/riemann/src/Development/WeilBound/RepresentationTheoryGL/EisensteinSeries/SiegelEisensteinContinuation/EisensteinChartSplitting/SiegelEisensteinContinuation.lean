import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.SiegelMultOf
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.EisensteinChartSplitting.SiegelEisensteinContinuationOf

namespace PositivityTheory.RgEis.Sp.Hd

open PositivityTheory.RgEis.Hd

theorem siegelEisensteinContinuation : GlobalTheory.Published.SiegelEisensteinContinuation :=
  Sp.siegelEisensteinContinuation_of dict dictInf secLaw (wallLaw_of secLaw) (cmGood_of stdGood dict dictInf) grpTop bdetLaw
    extLaw (parLaw_of bdetLaw extLaw grpTop) PositivityTheory.RgEis.Hd.sgAll

end PositivityTheory.RgEis.Sp.Hd
