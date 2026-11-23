import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellColumnsFrame
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionCellFl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_columns_frame : ∀ (ι : Type) [Fintype ι] (N : ℕ) (w : ι → Equiv.Perm (Fin N)) (τ : ι), VB.IsFrame (cellCol ι N w τ) := by
  first | exact @GlobalTheory.FlagZ.Univ.isFrame_cellCol | exact GlobalTheory.FlagZ.Univ.isFrame_cellCol | (intros; apply GlobalTheory.FlagZ.Univ.isFrame_cellCol <;> assumption)
