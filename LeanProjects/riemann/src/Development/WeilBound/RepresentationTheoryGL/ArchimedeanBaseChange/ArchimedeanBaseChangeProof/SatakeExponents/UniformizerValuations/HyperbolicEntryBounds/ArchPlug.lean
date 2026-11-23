import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.ArchTop
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.TrMulComm
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveFinal

namespace PositivityTheory.Rg.BcB.F.F0

open PositivityTheory.Rg.BcB.CG in
theorem archEx_of_compat (hC : PositivityTheory.Rg.BcB.CG.CompatEx) : PositivityTheory.Rg.BcB.F.ArchEx :=
  archimedean_existence_of_compatibility hC vcBridge PositivityTheory.RgBcC.wave_existence_speed_multiplicity.2.2.1

end PositivityTheory.Rg.BcB.F.F0
