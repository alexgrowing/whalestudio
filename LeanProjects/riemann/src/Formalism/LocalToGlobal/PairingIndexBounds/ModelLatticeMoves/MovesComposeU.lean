import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.ModelIndexPairings.FourierTransformIdentityHolds
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.ModelIndexPairings.GenModelXiOf
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.ModelIndexPairings.LinearExtensionHolds
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.ModelIndexPairings.RelIndexLeOfPairing

namespace Formalism.L2.PairingIndexBounds.Mv

theorem xiExists : XiExists := xi_existence_holds
theorem xiInter : XiInter := xi_intersection_holds
theorem moves : Moves := lattice_moves_hold
theorem indexDual : IndexDual := index_duality_holds
theorem extendLin : ExtendLin := linear_extension_holds
theorem heisU : HeisU := heisenberg_unitary_holds
theorem interSelf : InterSelf := self_intersection_holds
theorem movesU : MovesU := MovesU_of moves indexDual
theorem movesComposeU : MovesComposeU := MovesComposeU_of movesU xiExists xiInter
theorem genModelXi : GenModelXi := GenModelXi_of xiExists movesU extendLin

end Formalism.L2.PairingIndexBounds.Mv
