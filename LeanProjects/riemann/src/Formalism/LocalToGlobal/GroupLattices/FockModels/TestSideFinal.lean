import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSide
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FormCoreSK

namespace Formalism.L2.G.Model

theorem formCore : FormCore := TS.Top.formCoreSK

theorem testSide : Formalism.MainNotions.G.TestSide := testSide_of_core formCore

end Formalism.L2.G.Model
