import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HaarExists

namespace CompanionTheory.RgExh.Dec.L

open CompanionTheory.RgExh

theorem back_of (hA : Assembly) (h1 : AbsoluteL2Bound) (h2 : Geo) (h3 : LineFormula) (h4 : HaarExists) (h5 : PolyNilPath)
    (h6 : N.RightRule) (h7 : N.LeftRule) (h8 : KRight) (h9 : Growth) (h10 : Pack) : Back :=
  fun h0 => hA h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h0

end CompanionTheory.RgExh.Dec.L
