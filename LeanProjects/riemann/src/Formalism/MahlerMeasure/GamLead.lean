import Formalism.MahlerMeasure.FinalM
import Formalism.MahlerMeasure.MahlerMeasureProofs.GamDeg
import Formalism.MahlerMeasure.MahlerMeasureProofs.GamLead
import Formalism.MahlerMeasure.MahlerMeasureProofs.GamInt

namespace Formalism.GM.Top
open Formalism.GM
theorem gamDeg : M.GamDeg := gamma_degree_bound
theorem gamLead : M.GamLead := gamma_leading_term
theorem gamInt : M.GamInt := gamma_integrality
end Formalism.GM.Top
