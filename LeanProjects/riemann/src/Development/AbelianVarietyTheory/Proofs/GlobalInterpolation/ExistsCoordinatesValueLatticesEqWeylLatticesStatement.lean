import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsCoordinatesValueLatticesEqWeylLattices
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainSharpColumnValuationOfPointKernelLiftL
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coordinates_valueLattices_eq_weylLattices : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (M : PtModel B.ch i) (R : B.Real i sp M), i ≤ D.R.m → B.Sees → ∃ Co : M.Coord, Co.Ok ∧ R.ValIs Co := by
  first | exact @GlobalTheory.LvT.Built.ValLat.exists_coord | exact GlobalTheory.LvT.Built.ValLat.exists_coord | (intros; apply GlobalTheory.LvT.Built.ValLat.exists_coord <;> assumption)
