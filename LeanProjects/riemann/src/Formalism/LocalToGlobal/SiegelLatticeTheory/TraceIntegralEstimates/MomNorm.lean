import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.MomFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.Admissible

noncomputable section

namespace Formalism.L2.S.Pv.Mom

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

theorem momF' {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Cg cb Cu cT CT C0 : ℝ)
    (hBS : Formalism.MainNotions.S.Pv.Mom.BesselSchurF' Fm Cg cb Cu cT CT C0) (hM1 : Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOne) :
    Formalism.MainNotions.S.Pv.Mom.MomF' Fm Cg cb Cu cT CT C0 :=
  Formalism.MainNotions.S.Pv.Mom.momF'_of_schur Fm Cg cb Cu cT CT C0 hBS hM1 Formalism.L2.SG.Pf.k_finite_smooth_bessel

end Formalism.L2.S.Pv.Mom
