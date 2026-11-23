import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FourthPowerTheta

namespace GlobalTheory.ThLoc

theorem locJets_all :
    Formalism.L2.Th1.GD.IntOpLoc ∧ Formalism.L2.Th1.GD.IntOpTwoLoc ∧
      (Formalism.L2.Th1.GD.EmbSep → Formalism.L2.Th1.GD.ShapeEigenLoc) :=
  ⟨LocJets.jetsOdd, LocJets.jetsTwo, LocJets.shape⟩

end GlobalTheory.ThLoc
