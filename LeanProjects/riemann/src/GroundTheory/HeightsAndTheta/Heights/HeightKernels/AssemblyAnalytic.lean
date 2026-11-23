import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussTop
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussPoissonDual
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussSqrt
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussPoissonBound
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussLatticeIsLattice
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussLatticeCovolume
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussLatticeCoords
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussFourierSelf
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussDualMin
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussDetFactor
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussShellSum
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussShell
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussPacking
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussTermBound
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussConstant
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaTop
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaMean
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaInnerMean
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaSummandNorm
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaCubeParseval
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaCharIntegral
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaNormMajorant
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaFirstCoordSplit
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaConstants
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCauchyBinet
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPlueckerNormSq
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PHadamardPSD
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPlueckerUnitBound
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPlueckerKernel
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootsOfUnityDense
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem GaussianSum.full : GaussianSum.Statement :=
  GaussianSum.proof
    (GaussPoissonDual.proof GaussSqrt.proof
      (GaussPoissonBound.proof GaussLatticeIsLattice.proof
        (GaussLatticeCovolume.proof GaussLatticeIsLattice.proof) GaussLatticeCoords.proof
        GaussFourierSelf.proof)
      GaussDualMin.proof GaussDetFactor.proof)
    (GaussShellSum.proof (GaussShell.proof GaussPacking.proof GaussTermBound.proof))
    GaussConstant.proof

theorem ThetaMean.full : ThetaMean.Statement :=
  ThetaMean.proof
    (ThetaInnerMean.proof ThetaSummandNorm.proof
      (ThetaCubeParseval.proof ThetaCharIntegral.proof))

theorem ThetaBound.full : ThetaBound.Statement :=
  ThetaBound.proof GaussianSum.full ThetaMean.full
    (ThetaNormMajorant.proof ThetaSummandNorm.proof) ThetaFirstCoordSplit.proof ThetaConstants.proof

theorem PlueckerNormSq.full : PlueckerNormSq.Statement := PlueckerNormSq.proof CauchyBinet.proof

theorem PlueckerUnitBound.full : PlueckerUnitBound.Statement :=
  PlueckerUnitBound.proof HadamardPSD.proof

theorem PlueckerKernel.full : PlueckerKernel.Statement :=
  PlueckerKernel.proof PlueckerNormSq.full PlueckerUnitBound.full

theorem RootsOfUnityDense.full : RootsOfUnityDense.Statement := RootsOfUnityDense.proof

end GroundTheory.Heights₂.Heights
