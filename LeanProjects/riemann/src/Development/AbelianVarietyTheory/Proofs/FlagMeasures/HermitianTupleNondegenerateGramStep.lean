import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NormGramAtOrigin
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CovolumeSpans
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.VanishingOrbitalPoints
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalInvariants
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalCount
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlInvHolds

noncomputable section

open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic

namespace GlobalTheory.RowNGClosed

theorem ooVanish_all : ∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X)
    (u u' : D.what₂.Word),
    Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X) := by
  intro D X Y u u' t ht
  exact Formalism.L2.SG.TermOp.Vanish.ooVanish_of Formalism.L2.SG.Closed.AvgCore_holds Formalism.L2.SG.Pf.ginfUnimod_holds
    Formalism.L2.SG.Pf.nLamNinf_holds Formalism.L2.SG.Closed.ChiTrivialC_holds Formalism.L2.SG.Pf.psiInfChar_holds
    Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds
    Formalism.L2.SG.NonRelPf.nonRelCharC_holds Y t ht

theorem hermitian_tuple_nondegenerate_gram_step : NondegenerateGramTuple := by
  intro D X
  have hn : 2 * D.R.rS + 2 ≤ X.B.I.n := by
    have := X.n_eq; have := D.R.rS_two; have := D.R.r_eq; have := D.R.k_ge; omega
  have hH : ∀ i j, star (X.B.I.J j i) = X.B.I.J i j := fun i j => congrFun (congrFun X.B.I.J_herm i) j
  obtain ⟨X0, h0⟩ := exists_nondegenerate X.B.I.E X.B.I.n (2 * D.R.rS + 2) hn X.B.I.J hH X.B.I.J_det
  refine ⟨X0, ?_⟩
  convert h0 using 2
  ext a b
  rfl

theorem closedSteps : CorankOneEquivalence ∧ StepNormals ∧ StepPoints ∧ StepNormOne ∧ NondegenerateGramTuple := by
  have h1 : StepNormOne := VanishingOrbitalPoints.stepNormOne_of_ooVanish ooVanish_all
  exact ⟨CorankRelation.corankOne_equivalence_holds,
    NormalInvariants.stepNormals_of NormalVectorPairings.NmlInv_holds NormalCount.NormCount_holds h1,
    VanishingOrbitalPoints.stepPoints_of_ooVanish ooVanish_all, h1, hermitian_tuple_nondegenerate_gram_step⟩

end GlobalTheory.RowNGClosed
