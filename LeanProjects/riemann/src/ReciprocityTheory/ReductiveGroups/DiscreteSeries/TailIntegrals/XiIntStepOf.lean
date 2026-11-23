import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiRNonneg
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HermitianLiftIdentities

namespace ReciprocityTheory.ChartRestriction.DS.Xi

theorem iw : IW := iwB

theorem det_of (hB2 : InductiveHeisenbergInputs) : DET := detH hB2

theorem coefStep_of (hB2 : InductiveHeisenbergInputs) (hT : TBoth) (hD : DET) : CoefStep := CB.coefStepC hB2 hT hD

end ReciprocityTheory.ChartRestriction.DS.Xi
