import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFlagStalkSpan
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionCellFl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_flag_stalk_span : ∀ (ι : Type) [Fintype ι] (N : ℕ) (w : ι → Equiv.Perm (Fin N)) (τ : ι) (l : ℕ) (y : Fl ι N) (hy : y ∈ cellOpen ι N w), colSpan (Matrix.GeneralLinearGroup.map (((Fl ι N).presheaf.germ (cellOpen ι N w) y hy).hom.comp (cellRing ι N w)) (cellGL Prod.fst Prod.snd w τ)).1 l = Submodule.span _ {v | ∃ j : Fin N, (j : ℕ) < l ∧ v = (freeModule (Fl ι N) (Fin N)).presheaf.germ (cellOpen ι N w) y hy (cellCol ι N w τ j)} := by
  first | exact @GlobalTheory.FlagZ.Univ.colSpan_germ_cellGL | exact GlobalTheory.FlagZ.Univ.colSpan_germ_cellGL | (intros; apply GlobalTheory.FlagZ.Univ.colSpan_germ_cellGL <;> assumption)
