import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.ProdBlockEmbMonomial
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.FockPairingDividedAdjoint
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.FockPairingRowAction
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.FockPairingHighestWeightProof
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.CwlApplyWordAppendSingle
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.LowerTriangularOverField
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.WeylFormNondegenerateGlobal
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.FormSK

namespace Formalism.L2.G.Model.TS.Top

open Formalism.L2.G.Model.TS Formalism.GradedWeylDivisibility

theorem fockRBilin : FockRBilin := Formalism.L2.G.Model.TS.fock_pairing_bilinear
theorem fockRMap : FockRMap := Formalism.L2.G.Model.TS.fock_pairing_map
theorem fockRMonomial : FockRMonomial := Formalism.L2.G.Model.TS.fock_pairing_monomial
theorem fockRBlock : FockRBlock := Formalism.L2.G.Model.TS.fock_pairing_block
theorem hWNorm : HWNorm := Formalism.L2.G.Model.TS.highest_weight_norm
theorem fockRRowDivAdj : FockRRowDivAdj := Formalism.L2.G.Model.TS.fock_pairing_divided_adjoint
theorem fockRRowAct : FockRRowAct := Formalism.L2.G.Model.TS.fock_pairing_row_action
theorem fock_pairing_highest_weight : FockPairingHighestWeight := Formalism.L2.G.Model.TS.fock_pairing_highest_weight_proof
theorem weylPair : WeylPair := Formalism.L2.G.Model.TS.weyl_pairing
theorem dualWeylIn : DualWeylIn := Formalism.L2.G.Model.TS.dual_weyl_inclusion
theorem nondegK : NondegK := Formalism.L2.G.Model.TS.nondegenerate_over_field
theorem formCoreSK : FormCoreSK := Formalism.L2.G.Model.TS.formCoreSK_of Formalism.L2.G.Model.TS.weyl_form_nondegenerate_global

end Formalism.L2.G.Model.TS.Top
