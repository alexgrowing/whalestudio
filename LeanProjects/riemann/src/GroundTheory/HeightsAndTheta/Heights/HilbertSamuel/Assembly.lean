import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAnResToAnalyticRes
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageChi
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMonomialDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFSMass
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjectionBounds
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullFSExtension
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRealGramComparison
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResChiBounds
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResChiIndex
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseMonoBasis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem AnResToAnalyticRes.full : GroundTheory.Heights₂.Heights.HilbertSamuel.AnResToAnalyticRes.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.AnResToAnalyticRes.proof NonvanishingDense.full

theorem BlockImageChi.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageChi.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageChi.proof

theorem ResChiBounds.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResChiBounds.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResChiBounds.proof ResolutionSupBound.full

theorem ProjectionBounds.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjectionBounds.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjectionBounds.proof ResChiBounds.full

theorem PullFSExtension.full : GroundTheory.Heights₂.Heights.HilbertSamuel.PullFSExtension.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.PullFSExtension.proof ProjFrameBasePtFree.full

theorem ProjFSMass.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFSMass.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFSMass.proof

theorem RealGramComparison.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RealGramComparison.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RealGramComparison.proof ResolutionSupBound.full ProjectionBounds.full PullFSExtension.full

theorem MonomialDegree.full : GroundTheory.Heights₂.Heights.HilbertSamuel.MonomialDegree.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.MonomialDegree.proof

theorem ResChiIndex.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResChiIndex.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResChiIndex.proof

theorem VeroneseMonoBasis.full : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseMonoBasis.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseMonoBasis.proof

end GroundTheory.Heights₂.Heights.HilbertSamuel
