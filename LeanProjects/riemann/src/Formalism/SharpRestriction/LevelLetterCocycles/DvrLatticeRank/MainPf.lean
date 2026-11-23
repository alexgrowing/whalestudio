import Formalism.SharpRestriction.LevelLetterCocycles.LocalTheoremOfLeafLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.NormAHolds
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GeneratorBoundOfHypotheses
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UniformiserRingOfHypotheses
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.QuotPf
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.LiftPf
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ExtPfMultVEqZero
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.NinLamPf
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.OneGenPf
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GamPiPf
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FrobPiNPf
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ClassMapPf
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPf
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.KapPiPf
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DvdCondition
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.InvLiftPf
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FrobeniusSpanDecomposition
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.RankLinkProof
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UnivLinkPf
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ExponentRecursionHolds
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.WLocal
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U3uplinkPfOf
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DescentValuation
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.RankBounds
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U3mixlinkPf
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPf
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelQPf
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePf
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPf
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U2ringPfZetaO

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem lifting_theorem_of_uniform_link (hU1L : FirstFrameOfModels) :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
      (CA CB CK C : ℝ), 160 ≤ C → FontExAll D HW F → DdRFull D → DiRank D HW F Cm →
        IntegralityFromMetric D HW F Cm CA CB CK C :=
  local_theorem_of_leaf_lemmas generator_bound_of_hypotheses lift_bound_of_hypotheses DvdPf.dvdCondition quotient_jumps_subset normR_holds
    uniformiser_ring_of_hypotheses ExtPf.ext_pf w_pf kerlam2_pf ninlam_pf gradNCondition frobPiNCondition gamPiCondition
    OneGenPf.onegen_pf univlink_pf invLiftCondition ClassMapPf.classmap_pf frame_pf modelflink_pf
    exponent_recursion_holds modell_pf modelqlink_pf hU1L kappi_pf RankLink.rank_link_holds
    (RankBounds.u2rank_of_ring u2ring_pf) DescentValuation.down_of_models (u3uplink_pf_of w_pf) u3mixlink_pf

end Formalism.MainNotions.N.Ln34

end
