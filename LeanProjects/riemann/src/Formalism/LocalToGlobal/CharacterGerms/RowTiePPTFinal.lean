import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTTop
import Formalism.LocalToGlobal.CharacterGerms.RowTiePAllStart
import Formalism.LocalToGlobal.CharacterGerms.EndomorphismLimitIntegral
import Formalism.LocalToGlobal.CharacterGerms.RowTiePProjFBTop

namespace Formalism.L2.FormalSeriesBounds

theorem allStartFB_of_proj (hP : ProjFBSt) : AllStartFBSt := by
  intro C _ _ V O _ _ dd Y d _ I _ p g w hw
  exact allStart_of_proj Y p (hP C V O dd Y d I p (RowTiePE0.endomorphism_limit_all C V O dd Y)) g w hw

theorem ptFB_of_proj (hP : ProjFBSt) (hStab : HStabFBSt) : PTFBSt :=
  ptFB_of_start3 (allStartFB_of_proj hP) hStab

theorem cartFB_of_proj (hP : ProjFBSt) (hStab : HStabFBSt) : CartFBSt :=
  cartFB_of_start (allStartFB_of_proj hP) hStab

theorem ptFB_of_lie (hLie : RowTiePProj.ProjLieSt) (hStab : HStabFBSt) : PTFBSt :=
  ptFB_of_proj (RowTiePProj.projFB_of_lie hLie) hStab

end Formalism.L2.FormalSeriesBounds
