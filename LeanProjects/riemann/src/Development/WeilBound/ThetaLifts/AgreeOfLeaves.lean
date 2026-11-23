import Development.WeilBound.ThetaLifts.ConeHypotheses.CtSmallCone

namespace PositivityTheory.ThKG

open GlobalTheory.ThK GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem agree_of_leaves (L : Leaves) (hd : KDecay) (hc : KCoinv) : ThetaIntegralsAgree ∧ LocalMatching :=
  ⟨agree_of_parts hd L.kConst hc L.kBeta L.kAlpha, matching_of_parts L.kReal L.kFin⟩

end PositivityTheory.ThKG
