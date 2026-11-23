import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.CechDelta

theorem terminalEquiv_δ {X : TopCat.{0}} {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact) (n : ℕ)
    (y : Sheaf.H'.{0} S.X₃ n (⊤ : Opens X)) :
    GlobalTheory.SiteCoh.terminalEquiv S.X₁ (n + 1) isTerminalTop (GlobalTheory.SheafLES.δ hS n ⊤ y) =
      H.δ hS n (n + 1) rfl (GlobalTheory.SiteCoh.terminalEquiv S.X₃ n isTerminalTop y) := by
  exact (Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ (GlobalTheory.SiteCoh.freeSheafIsoConst isTerminalTop).inv) y hS.extClass (zero_add n) rfl (by omega)).symm

theorem hPull_δ {X Y : TopCat.{0}} (f : X ⟶ Y) {S : ShortComplex (AbSheaf Y)} {S' : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) (hS' : S'.ShortExact) (α : S ⟶ S'.map (push f)) (n : ℕ) (x : Sheaf.H.{0} S.X₃ n) :
    hPull f α.τ₁ (n + 1) (H.δ hS n (n + 1) rfl x) = H.δ hS' n (n + 1) rfl (hPull f α.τ₃ n x) := by
  obtain ⟨y, rfl⟩ : ∃ y, GlobalTheory.SiteCoh.terminalEquiv S.X₃ n isTerminalTop y = x :=
    ⟨_, AddEquiv.apply_symm_apply _ x⟩
  rw [← terminalEquiv_δ hS n y]
  dsimp only [hPull, GlobalTheory.SheafPull.pull, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  erw [GlobalTheory.SheafPull.sitePull_δ (TopologicalSpace.Opens.map f) hS hS' α n]
  exact terminalEquiv_δ hS' n _

end GlobalTheory.CompanionTheory.CechDelta
