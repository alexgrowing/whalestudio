import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.GramBoundOfRestrictionOfProj
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.HighestVectorProjection
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.ResSat
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.DerivativeKeepsSpaceHolds
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.OmegaInjectiveHolds
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.MulEarlyLettersModP

namespace Formalism.InvariantFactorPaths.L4.Top

open Formalism.InvariantFactorPaths.L4

theorem uComm : UComm := raising_comm_holds
theorem uKeepsLast : UKeepsLast := raising_keeps_last_letter
theorem uKeepsEarly : UKeepsEarly := raising_keeps_early_letters
theorem uDeg : UDeg := raising_degree_holds
theorem resU : ResU := restriction_raising_holds
theorem dKeepsX : DKeepsX := derivative_keeps_space_holds
theorem sl2Inj : Sl2Injective := sl2_injectivity_holds
theorem eArith : EArith := exponent_arithmetic_holds
theorem omegaInj : OmegaInj := omega_injective_holds
theorem resOntoKThm : ResOntoKThm := resOntoKThm_of omega_injective_holds
theorem dpowInt : DpowInt := divided_power_integral
theorem modOfY : ModOfY := mod_p_of_conditions
theorem mulEarlyModP : MulEarlyModP := mul_early_letters_mod_p
theorem mulLastModP : MulLastModP := mul_last_letter_mod_p
theorem divModPOf : DivModPOf := divided_power_mod_p_of

end Formalism.InvariantFactorPaths.L4.Top
