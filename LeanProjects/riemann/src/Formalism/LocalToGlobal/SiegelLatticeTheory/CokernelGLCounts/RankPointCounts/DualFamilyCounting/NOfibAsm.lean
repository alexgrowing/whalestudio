import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibRat
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibPl
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.InvMulOfUnitri
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibLatF
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibLatB
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibOnto

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

theorem nofibLat_of_rest (hL : DictLat) (hE : DictEx) (hF : FibQ) (hO : FibOnto) : NOfibLat := by
  have hR : NOratC := by first | exact @noratC_holds | exact @noratC_proved | exact @noratC | exact @nOratC_holds | exact @noratC_of | exact @NOratC_holds
  have hG : DictGram := by first | exact @dictGram_holds | exact @dictGram_proved | exact @dictGram | exact @DictGram_holds | exact @dictGram_of
  have hP : DictPlace := by first | exact @dictionary_place_holds | exact @dictPlace_holds | exact @dictPlace_proved | exact @dictPlace | exact @DictPlace_holds | exact @dictPlace_of
  exact @nofibLat_of hR hG hL hE hP hF hO

theorem nofib_of_rest (hL : DictLat) (hE : DictEx) (hF : FibQ) (hO : FibOnto) : NOfib := @Formalism.L2.SG.Pf.NcReal.JX.nofib_of (@nofibLat_of_rest hL hE hF hO)

theorem nOfib_of_dict_fib (hB : DictLatB) (hF : FibQ) (hO : FibOnto) : NOfib := by
  have hLF : DictLatF := by first | exact @dictLatF_proof | exact @dictLatF_holds | exact @dictLatF_proved | exact @dictLatF | exact @DictLatF_holds | exact @dictLatF_of
  have hL : DictLat := @dictLat_of hLF hB
  have hE : DictEx := @Ex.dictEx_holds
  exact @nofib_of_rest hL hE hF hO

theorem nofib_of_fib (hF : FibQ) (hO : FibOnto) : NOfib := by
  have hB : DictLatB := by first | exact @dictLatB_proof | exact @dictLatB_holds | exact @dictLatB_proved | exact @dictLatB | exact @DictLatB_holds | exact @dictLatB_of
  exact @nOfib_of_dict_fib hB hF hO

theorem nofib_of_fibQ (hF : FibQ) : NOfib := by
  have hO : FibOnto := by first | exact @fibOnto_proof | exact @fibOnto_holds | exact @fibOnto_proved | exact @fibOnto | exact @FibOnto_holds | exact @fibOnto_of
  exact @nofib_of_fib hF hO

end Formalism.L2.SG.Pf.NcReal.JX.NOf
