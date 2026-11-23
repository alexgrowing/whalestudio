import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FramesMem
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlLineHolds

namespace Formalism.L2.SG.NGCut.NormalIntegrality

theorem NmlInt_holds : Formalism.L2.SG.NGCut.NormalVectorPairings.NmlInt :=
  nmlInt_of fun _ _ Y _ _ t0 t h0 h hR hG hT hT' =>
    ⟨(Formalism.L2.SG.NGCut.NormalVectorPairings.line_occ Y t0 t h0 h hR hG hT hT').1.1,
      (Formalism.L2.SG.NGCut.NormalVectorPairings.line_occ Y t0 t h0 h hR hG hT hT').2.1⟩

end Formalism.L2.SG.NGCut.NormalIntegrality
