import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IsometryTransportFrames
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFundamentalDomainIffImageHA
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFundamentalDomainMap

namespace GlobalTheory.VolIndepClosed

theorem volIndep (D : Formalism.BasicNotions.D7) : GlobalTheory.IndefiniteRowSideFullHecke.IsometryTransportFrames.VolIndep D :=
  (GlobalTheory.VolIndepCompare.volumeIndependence_iff D).1 (GlobalTheory.VolumeIndep.volumeIndependence D)

end GlobalTheory.VolIndepClosed
