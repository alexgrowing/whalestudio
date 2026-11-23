import Development.WeilBound.ThetaLifts.SmallCones.SoZero
import Development.WeilBound.ThetaLifts.SmallCones.LinExOf

namespace PositivityTheory.ThKCT

theorem soEv_of' (hLow : Low) : SoEv := soEv_of linEx_of hLow

theorem soZeroA'_of' (hX : PositivityTheory.ThKG.MixX) (hE : ThetaExp) (hU : EvUniq) : SoZeroA' := soZeroA'_of linEx_of hX hE hU

end PositivityTheory.ThKCT
