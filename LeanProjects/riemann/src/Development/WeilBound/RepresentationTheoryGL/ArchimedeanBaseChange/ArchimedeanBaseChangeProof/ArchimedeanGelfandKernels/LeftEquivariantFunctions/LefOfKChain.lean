import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.LefTop
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveFinal

namespace PositivityTheory.RgBcC

theorem lef_of_kChain (hC : LfSt.KChain) : Lef :=
  lef_top wave_existence_speed_multiplicity.1 wave_existence_speed_multiplicity.2.1 wave_existence_speed_multiplicity.2.2.1 wave_existence_speed_multiplicity.2.2.2 hC

end PositivityTheory.RgBcC
