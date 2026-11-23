import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowsOfAllPartProperties
import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rows_of_all_part_properties : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : Ind.Part D O c), Ind.PFire D O c b → Ind.PRB D O c b → Ind.PPA D O c b → Ind.PFrames D O c b → Ind.PDiv D O c b → Ind.PNmj D O c b → Formalism.BasicNotions.GoodFTAll D → b.pt.Ties → Ind.PRows D O c b := by
  first | exact @GlobalTheory.Fc.Ind.pRows_of_parts | exact GlobalTheory.Fc.Ind.pRows_of_parts | (intros; apply GlobalTheory.Fc.Ind.pRows_of_parts <;> assumption)
