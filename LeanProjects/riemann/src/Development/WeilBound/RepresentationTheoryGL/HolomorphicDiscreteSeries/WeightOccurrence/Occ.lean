import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.LowestKTypeModels.Models
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.IntertwinerAdjoints.Imports
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.FlipDecomposition.DecompositionExistenceHolds
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.Imports
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.StepM
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.FarClosed

namespace PositivityTheory.RgHe

theorem occ : Occ :=
  Dec.walk (Sl.stepL LowestKTypeModel.models LowestKTypeModel.ofInt LowestKTypeModel.seed Dec.decomposition_existence_holds)
    (SM.stepM LowestKTypeModel.models LowestKTypeModel.ofInt LowestKTypeModel.seed Dec.decomposition_existence_holds)
    (PositivityTheory.RgHe3.base LowestKTypeModel.models FrameF.frame)

end PositivityTheory.RgHe
