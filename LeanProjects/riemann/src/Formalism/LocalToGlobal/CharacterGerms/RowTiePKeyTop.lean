import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyGlue
import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyDelta
import Formalism.LocalToGlobal.CharacterGerms.RowTiePSplitLA

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKey

theorem projFB_of_eig_res (hE : KeyEigSt) (hR : KeyResSt) : ProjFBSt :=
  RowTiePProj.projFB_of_lie (RowTiePLie.projLie_of (key_of hE hR keyDelta_holds) RowTiePSplit.split_holds)

end RowTiePKey

end Formalism.L2.FormalSeriesBounds
