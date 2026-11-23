import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionCellFl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

theorem GlobalTheory.FlagZ.Univ.colSpan_germ_cellGL : ∀ (ι : Type) [Fintype ι] (N : ℕ) (w : ι → Equiv.Perm (Fin N)) (τ : ι) (l : ℕ) (y : Fl ι N) (hy : y ∈ cellOpen ι N w), colSpan (Matrix.GeneralLinearGroup.map (((Fl ι N).presheaf.germ (cellOpen ι N w) y hy).hom.comp (cellRing ι N w)) (cellGL Prod.fst Prod.snd w τ)).1 l = Submodule.span _ {v | ∃ j : Fin N, (j : ℕ) < l ∧ v = (freeModule (Fl ι N) (Fin N)).presheaf.germ (cellOpen ι N w) y hy (cellCol ι N w τ j)} := by
  intro ι _ N w τ l y hy
  unfold colSpan
  congr 1
  ext v
  simp only [Set.mem_setOf_eq, Matrix.GeneralLinearGroup.map_apply, cellCol, map_sum, GlobalTheory.QCoh.germ_smul,
    GlobalTheory.Twist.germ_resM, stalkStd, RingHom.comp_apply]
  refine exists_congr fun j => and_congr_right fun _ => ?_
  refine Eq.congr_right (Finset.sum_congr rfl fun i _ => ?_)
  exact congrArg _ (VB.IsFrame.stalkBasis_apply _ _ _ _)
