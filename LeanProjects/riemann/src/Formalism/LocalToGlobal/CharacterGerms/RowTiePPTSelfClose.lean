import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTClose
import Formalism.LocalToGlobal.CharacterGerms.RowTiePStartSelf

namespace Formalism.L2.FormalSeriesBounds

theorem ptSelf_of_lieSelf (h : ProjLieSelfSt) : PTSelfSt := ptSelf_of_start2 (allStartSelf_of h)

end Formalism.L2.FormalSeriesBounds
