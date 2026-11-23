import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.OneLeAbsNormOfLeOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois

namespace Formalism.L2.LamCM

theorem cm_numbers_link : CMNumbersLink := CMNumbersLink_of hadamardIdeals detLineAdmissible

theorem degree_delta : DegDe := DegDe_of hadamardIdeals detLineAdmissible

theorem degree_norm : DegNN := DegNN_of hadamardIdeals detLineAdmissible

theorem lambda_number : LamNumber := LamNumber_of hadamardIdeals detLineAdmissible

end Formalism.L2.LamCM
