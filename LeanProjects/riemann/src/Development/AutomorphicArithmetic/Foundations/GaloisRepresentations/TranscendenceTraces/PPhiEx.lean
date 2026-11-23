import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PhiAsm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPhiUniv
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PDSOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PDSLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPhiExact

namespace UpperTheory.Gal.TranscendenceTraces

theorem phiEx_of : LocFinSec → PhiEx := fun h => phiEx_of_parts phiUniv_of (phiExact_of (dSLoc_of (dSOne_of h)))

end UpperTheory.Gal.TranscendenceTraces
