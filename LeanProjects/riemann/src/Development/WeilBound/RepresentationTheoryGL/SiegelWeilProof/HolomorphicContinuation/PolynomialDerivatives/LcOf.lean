import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.LcOfCore
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.CoreTop

namespace PositivityTheory.Rg.Sw

theorem lc_of (h : FFT) : LC := LC.lc_of_core (LC.coreLC_of h)

end PositivityTheory.Rg.Sw
