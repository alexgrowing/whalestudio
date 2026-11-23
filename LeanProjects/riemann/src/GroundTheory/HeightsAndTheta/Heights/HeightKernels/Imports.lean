import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Statements
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblyAnalytic
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblySympl
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblyLines
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.CoordFirst
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.CoordSiegel
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.CoordWeak
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ShortVectors
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AltRow
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AltPush
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AltFrob
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestTop
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem KernelsCut.proof (h₇ : LineOfLargeDegree.Statement) (h₉ : RestTermSharp.Statement) :
    KernelsCut.Statement :=
  ⟨SymplecticReduction.full, SiegelCoordinates.intersectionNumber_baseChange, FirstCoordinateBound.intersectionNumber_baseChange, GaussianSum.full,
    ThetaBound.full, WeakMatrixArithmetic.intersectionNumber_baseChange, OrthogonalLines.full, h₇, ShortVectors.intersectionNumber_baseChange,
    RestTerm.proof h₉, h₉, AlternantRowRule.intersectionNumber_baseChange, AlternantPush.intersectionNumber_baseChange,
    FrobeniusRectangleBound.intersectionNumber_baseChange⟩

end GroundTheory.Heights₂.Heights
