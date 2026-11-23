import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesCoverExists

namespace PositivityTheory.RgFd.B

open PositivityTheory.RgDs

theorem fdAll : FdAll := fdAll_of_key K.key_identity_holds Hilb.hilbert_space_realisation_holds

theorem formalDegreeCompactDual : GlobalTheory.Published.FormalDegreeCompactDual := realMetaplectic_of_forall fdAll

end PositivityTheory.RgFd.B
