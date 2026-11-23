import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSquareTransferIdentityHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNormDegGBetaInfAbs
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BXiAsm
import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecLowPf
import Development.WeilBound.CoreStatements.BetaInfinityCoefficients.BetaInfinityCoefficient
import CompanionTheory.AutomorphicTheory.SchurLimitBounds.SchurOrthogonality.SchurH
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.UniformCoefficientBounds.FromDS
import CompanionTheory.AutomorphicTheory.RankOneEstimates.DecSender

noncomputable section

namespace CompanionTheory.D.Upq.Coef

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P.CutBP.Jmu Formalism.FourierDecayAlt.P.CutBP.Jmu.NDG

theorem normDegree_bound {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] [CompleteSpace Wp] [CompleteSpace Wq] (p : KB.Pl P Wp Wq) :
    NormDegG p :=
  normDegG_of_leaves norm_square_transfer_identity_holds capelli_coefficient_continuity beta_infinity_absolute_bound MainStatements.BetaInf.betaInfinity_coefficient
    Formalism.FourierDecayAlt.P.b_any_of_xi CompanionTheory.LimBd.SchurHpk.threeDimData_schurH
    CompanionTheory.D.gk.admitted.k_finite_smooth p

end CompanionTheory.D.Upq.Coef

end
