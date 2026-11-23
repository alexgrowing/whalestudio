import Formalism.SharpRestriction.GlobalSchurBounds.RamifiedLevelZeroHolds
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfGappedMultiplicity

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT

variable {eps : ℝ}

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem Wire.famGLmin_of_realPlaceSecondLayer (𝒞 : FamClass) (tie : Closed 𝒞 fun Fm _ => RealPlaceSecondLayerConditions Fm)
    (hU : ∀ D, MassRatioUnderVolume D) (hG : ∀ D, GenusMassVolumes.GenusMassAt D 2) :
    Wire.FamGLmin 𝒞 4 where
  h2b := Closed.of_all fun Fm _ => GenusMassVolumes.siegel_mass_ratio_family Fm
  h2v := tie.imp fun Fm _ _ t => family_property_mono (family_conditions_of_layer_two Fm t).1 fun D hT =>
    GenusMassVolumes.volume_eq_mass_rank_two D (StandardLattice.volumeMass_of_unfolding D (hU D hT)) (GenusMassVolumes.volume_mass_of_genus_rank D 2 hT (hG D))
  h3 := Closed.of_all fun Fm _ => GappedMultiplicityBounds.explicit_bound_family Fm
  hZa := Closed.of_all fun Fm _ => TraceIntegrality.lower_slope_inequality_family Fm
  hZb := Closed.of_all fun Fm _ => TraceIntegrality.slope_inequality_family_four Fm
  tCV := tie.imp fun Fm _ _ t => tCV_of_ties Fm (family_conditions_of_layer_two Fm t).2.1
  hW := tie.imp fun Fm _ _ t =>
    (slope_free_branch_family Fm (family_conditions_of_layer_two Fm t).2.2 freeTT_holds slopeLineT_holds LemB.second_branch_all_members).1
  hμ := tie.imp fun Fm _ _ t =>
    (slope_free_branch_family Fm (family_conditions_of_layer_two Fm t).2.2 freeTT_holds slopeLineT_holds LemB.second_branch_all_members).2.1
  hI := tie.imp fun Fm _ _ t => hI_tied Fm (family_conditions_of_layer_two Fm t).2.2 PI.IntegralAtBasePointLattice.integral_at_t0_lattice
  hR := tie.imp fun Fm _ _ t => ramified_level_zero_holds Fm (family_conditions_of_layer_two Fm t).2.2
  hB := tie.imp fun Fm _ _ t =>
    (slope_free_branch_family Fm (family_conditions_of_layer_two Fm t).2.2 freeTT_holds slopeLineT_holds LemB.second_branch_all_members).2.2

end Formalism.MainNotions

end
