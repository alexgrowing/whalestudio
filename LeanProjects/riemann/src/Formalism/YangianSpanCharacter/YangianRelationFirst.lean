import Formalism.YangianSpanCharacter.YangianRTTProofs.TransposeSymplecticShift
import Formalism.YangianSpanCharacter.YangianRTTProofs.RttRelation
import Formalism.YangianSpanCharacter.YangianRTTProofs.SymplecticTransposeEntryZeroOne
import Formalism.YangianSpanCharacter.YangianRTTProofs.DiagonalEntryEqOfModularRelation
import Formalism.YangianSpanCharacter.YangianRTTProofs.SpanCharacterIdentity
import Formalism.YangianSpanCharacter.ModHypYangian
import Formalism.YangianSpanCharacter.YangianRTTProofs.MinusFrameIdentity
import Formalism.YangianSpanCharacter.YangianRTTProofs.TransposeJReversed
import Formalism.YangianSpanCharacter.YangianRTTProofs.TransposeJTransposeReal

namespace Formalism.YangianSpanCharacter.Final

theorem T_PlaneWave : Formalism.YangianSpanCharacter.T.PlaneWave := Formalism.YangianSpanCharacter.P.planeWaveIntertwining
theorem T_UJU : Formalism.YangianSpanCharacter.T.UJU := Formalism.YangianSpanCharacter.P.unipotentSymplectic
theorem T_WeylModel : Formalism.YangianSpanCharacter.T.WeylModel := Formalism.YangianSpanCharacter.P.isWeylTripleShiftModel
theorem Y_ModHypModel : Formalism.YangianSpanCharacter.Y.ModHypModel := Formalism.YangianSpanCharacter.P.isLaxFamilyConstantModel
theorem E_GGRatio : Formalism.YangianSpanCharacter.E.GGRatio := Formalism.YangianSpanCharacter.P.gamma_ratio_identity
theorem E_GGProd : Formalism.YangianSpanCharacter.E.GGProd := Formalism.YangianSpanCharacter.P.gamma_product_identity
theorem B_TJTReal : Formalism.YangianSpanCharacter.B.TJTReal := Formalism.YangianSpanCharacter.P.transpose_j_transpose_real
theorem B_TvJTsReal : Formalism.YangianSpanCharacter.B.TvJTsReal := Formalism.YangianSpanCharacter.P.twisted_j_transpose_real
theorem B_RTTReal : Formalism.YangianSpanCharacter.B.RTTReal := Formalism.YangianSpanCharacter.P.rtt_real

end Formalism.YangianSpanCharacter.Final
