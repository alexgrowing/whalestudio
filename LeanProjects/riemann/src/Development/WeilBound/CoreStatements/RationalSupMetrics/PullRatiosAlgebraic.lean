import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallPacking
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsRankBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecMRankBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionsSeparated
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecEq
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConductor
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootGridLower
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGridSeparation
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNormalLocusRep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjAvoidingForm
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegreArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreRepresentatives
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAvoidFormFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormMax
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMetricMaxComparison
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullFormsGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullRatiosAlgebraic
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullConeNull
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullConeDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullGradedAlgebraic
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormDehomCharpoly
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDehomCharpolyForms
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormDehomIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullSectionIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormBadPrimesFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormGoodPrimeIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormPrimeBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormDehomRoots
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullConeDegreeInt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullSectionIntegralInt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDehomNormPIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartPrimePowerInverse
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFibreNormPullbackX
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PullbackConeNullModPHoldsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormFormGaussBoundHoldsStatement

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel

namespace MultiProjectiveCoordinates

theorem pull_ratios_algebraic : PullRatiosAlgebraic.Statement :=
  PullRatiosAlgebraic.proof PullConeNull.proof PullConeDegree.proof PullGradedAlgebraic.proof

theorem pull_forms_generic : PullFormsGeneric.Statement := PullFormsGeneric.proof pull_ratios_algebraic

theorem fibre_pull_integral : FibreNormPullback.Statement :=
  FibreNormPullback.proof_dehom pull_forms_generic
    (FibreNormDehomCharpoly.proof pull_forms_generic pull_ratios_algebraic PullSectionIntegral.proof
      DehomCharpolyForms.proof)
    (FibreNormDehomIntegral.proof FibreNormBadPrimesFinite.proof
      (FibreNormGoodPrimeIntegral.proof GlobalTheory.T.pullback_cone_null_mod_p_holds PullConeDegreeInt.proof PullSectionIntegralInt.proof
        DehomNormPIntegral.proof)
      (FibreNormPrimeBound.proof pull_forms_generic GlobalTheory.T.norm_form_gauss_bound_holds ChartPrimePowerInverse.proof))
    FibreNormDehomRoots.full

theorem grid_separation : GridSeparation.Statement :=
  GridSeparation.proof NormalLocusRep.proof
    (FibreNormBound.proof (ProjAvoidingForm.proof SegreArith.proof)
      (FibreRepresentatives.proof AvoidFormFinite.proof)
      (FibreNormMax.proof fibre_pull_integral) MetricMaxComparison.proof)
    RootGridLower.proof

end MultiProjectiveCoordinates

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology in
theorem MultiProjectiveCoordinates.packing_statement : PackingStatement :=
  SmallPacking.proof
    (NmSectionsRankBound.proof (NmSectionsFinite.proof (Conductor.proof SecEq.proof)) SecMRankBound.full)
    (SmallSectionsSeparated.proof MultiProjectiveCoordinates.grid_separation)
