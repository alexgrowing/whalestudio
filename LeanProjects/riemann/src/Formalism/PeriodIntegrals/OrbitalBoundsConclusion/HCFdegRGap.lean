import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeGap.HCFdegRGapHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeGap.DimensionBoundOfGapUniform
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeGap.DimensionFamilyOfWeylMultiplicity
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremThreeHypothesesOfMultiplicity

noncomputable section

namespace PI

theorem hc_degree_gap : PI.UnitaryGroupMassFormula.HCFdegRGap.HCFdegRGap :=
  PI.UnitaryGroupMassFormula.HCFdegRGap.hCFdegRGap_holds

theorem explicitConstants_of_weylDimension (hW : Formalism.MainNotions.DiscreteSeriesWeylDimension.WeylForK) (hL : Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOne) : Formalism.MainNotions.RT.DiscreteSeriesDegreeBoundsAllScales :=
  PI.UnitaryGroupMassFormula.HCFdegRGap.dimension_bound_of_gap_uniform hc_degree_gap hW hL

theorem family_constants_low_k_type {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (hL : Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOne) :
    Formalism.MainNotions.flipTwoThree.fam0 Fm Formalism.MainNotions.StandardLattice.SigmaDegreeTwoSidedBoundOfGap :=
  PI.UnitaryGroupMassFormula.HCFdegRGap.dimension_family_of_weyl_multiplicity Fm Formalism.MainNotions.StandardLattice.weylForK_holds hL

end PI
