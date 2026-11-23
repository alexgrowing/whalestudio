import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.DDForm
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.AtFormAdm
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BesselNonvanishingL2

namespace CompanionTheory.Lime.BM

open Formalism.FourierDecayAlt.P CompanionTheory.D.Upq

theorem shape (hU : UniqGap) : Shape := by
  exact shape_of hU PI.WBL.S5.psiConst PI.WBL.NIS.schurH BesselFunctionalConstruction.beConv BesselFunctionalConstruction.normIdSm BesselFunctionalConstruction.beBessel

theorem dDFormOne (hU : UniqGap) : DDFormOne := by
  exact Formalism.FourierDecayAlt.P.DDSmoothness.BM.discrete_form_one_side PI.WBL.S5.psiConst PI.WBL.NIS.schurH
    Formalism.FourierDecayAlt.P.norm_inverse_bound Formalism.FourierDecayAlt.P.growth_spherical_bound Formalism.FourierDecayAlt.P.growth_group_bound BesselFunctionalConstruction.decDD BesselFunctionalConstruction.beConv
    BesselFunctionalConstruction.normIdSm BesselFunctionalConstruction.beBessel (shape hU)

theorem atFormAdmOne (hU : UniqGap) : AtFormAdmOne := by
  exact Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.BM.smooth_admissible_form_one_side PI.WBL.NIS.schurH BesselFunctionalConstruction.beConv BesselFunctionalConstruction.normIdSm
    BesselFunctionalConstruction.beBessel (shape hU) BesselFunctionalConstruction.kFinForm BesselFunctionalConstruction.zeroCase BesselFunctionalConstruction.zeroCaseDD

end CompanionTheory.Lime.BM
