import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelRowsEqDimensionAllStatement

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc.Ind

theorem pRows_of_parts : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : Ind.Part D O c), Ind.PFire D O c b → Ind.PRB D O c b →
    Ind.PPA D O c b → Ind.PFrames D O c b → Ind.PDiv D O c b → Ind.PNmj D O c b → Formalism.BasicNotions.GoodFTAll D → b.pt.Ties →
    Ind.PRows D O c b := by
  intro D O c b hF hB hP hFr hD hN hG hT
  exact
    { exAt := hF.1
      jEvBar := hF.2.1
      geoAct := hF.2.2.1
      evInj := hF.2.2.2
      ioExt := hB.ioExt
      oneMap := hB.oneMap
      prim := hP.1
      sep := hP.2
      ok := b.ok1
      framesOK := b.B.Q.frames hFr
      divRows := hD
      psi := b.psi
      d0 := GlobalTheory.T.base_level_rows_eq_dimension_all D O c b
      export_ := hN
      goodFT := hG
      w1 := fun w hw => ((b.muDef 0 0).2.2.2 w).2 hw
      ties := hT }

end GlobalTheory.Fc.Ind
