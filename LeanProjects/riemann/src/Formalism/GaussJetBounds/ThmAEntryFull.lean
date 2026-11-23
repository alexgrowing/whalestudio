import Formalism.GaussJetBounds.StatementX
import Formalism.GaussJetBounds.OneLetterGauss
import Formalism.GaussJetBounds.GaussJetProofs.SlopeBoundSaturation
import Formalism.GaussJetBounds.GaussJetProofs.OrbMul

namespace Formalism.DworkPowerSeriesWeights

theorem thmAEntryFull : ThmAEntryFull := by
  intro l _ d N0 N1 _ h3 h2 he K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I nu1 nu2 size
    hn1 hn2 hsz a ha hsa hthr δ hδ
  exact thmAEntry l d N0 N1 h3 h2 he K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I nu1 nu2
    size hn1 hn2 hsz a ha hsa hthr (slope_bound_saturation _ d N0 colN p hp) δ hδ

end Formalism.DworkPowerSeriesWeights
