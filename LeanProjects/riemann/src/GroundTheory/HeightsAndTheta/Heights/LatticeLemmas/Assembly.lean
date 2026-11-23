import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PBaseChange
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PSublattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PLatticeOfLocalisations
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PLocalChange
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PNormComparison
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PDiagonalChange
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PExactSequence
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PChainSum
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PHadamard
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PHadamardQuotient
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PHadamardMean
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PHadamardMeanQuotient
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PGaussNormBasic
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PSchwartzZippelPerVariable
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PRootsOfUnityValuation
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PHeightOfPoint
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PHeightOfCycle
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PSphereLawUnitary
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PSpherePhase
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PSphereProjectionLaw
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PPointwiseLelong
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v w

namespace LatticeLemmas

theorem BaseChange.full : BaseChange.Statement := BaseChange.proof

theorem Sublattice.full : Sublattice.Statement := Sublattice.proof

theorem LatticeOfLocalisations.full : LatticeOfLocalisations.Statement :=
  LatticeOfLocalisations.proof

theorem LocalChange.full_of_localIndex (h : LocalIndex.Statement.{u, v}) :
    LocalChange.Statement.{u, v} :=
  LocalChange.proof Sublattice.full h

theorem NormComparison.full : NormComparison.Statement := NormComparison.proof

theorem DiagonalChange.full : DiagonalChange.Statement := DiagonalChange.proof

theorem ExactSequence.full : ExactSequence.Statement := ExactSequence.proof

theorem ChainSum.full : ChainSum.Statement.{u, v} := ChainSum.proof ExactSequence.full

theorem Hadamard.full : Hadamard.Statement.{u, v, w} := Hadamard.proof Sublattice.full

theorem HadamardQuotient.full : HadamardQuotient.Statement.{u, v, w} :=
  HadamardQuotient.proof Hadamard.full

theorem HadamardMean.full : HadamardMean.Statement.{u, v, w} := HadamardMean.intersectionNumber_baseChange

theorem HadamardMeanQuotient.full : HadamardMeanQuotient.Statement.{u, v, w} :=
  HadamardMeanQuotient.proof HadamardMean.full

end LatticeLemmas

theorem GaussNormBasic.full : GaussNormBasic.Statement := GaussNormBasic.proof

theorem SchwartzZippelPerVariable.full : SchwartzZippelPerVariable.Statement :=
  SchwartzZippelPerVariable.proof

theorem RootsOfUnityValuation.full : RootsOfUnityValuation.Statement :=
  RootsOfUnityValuation.proof

theorem HeightOfPoint.full : HeightOfPoint.Statement := HeightOfPoint.proof GaussNormBasic.full

theorem HeightOfCycle.full_of_fibreMahlerForms (h : FibreMahlerForms.Statement) :
    HeightOfCycle.Statement :=
  HeightOfCycle.proof HeightOfPoint.full h

theorem SphereLawUnitary.full : SphereLawUnitary.Statement := SphereLawUnitary.proof

theorem SpherePhase.full_of_sphereLawBasic (hb : SphereLawBasic.Statement) :
    SpherePhase.Statement :=
  SpherePhase.proof hb SphereLawUnitary.full

theorem SphereProjectionLaw.full_of (hb : SphereLawBasic.Statement)
    (hc : SphereLawFirstCoord.Statement) : SphereProjectionLaw.Statement :=
  SphereProjectionLaw.proof hb SphereLawUnitary.full hc (SpherePhase.full_of_sphereLawBasic hb)

theorem PointwiseLelong.full_of (hb : SphereLawBasic.Statement)
    (hc : SphereLawFirstCoord.Statement) : PointwiseLelong.Statement :=
  PointwiseLelong.proof (SphereProjectionLaw.full_of hb hc)

end GroundTheory.Heights₂.Heights
