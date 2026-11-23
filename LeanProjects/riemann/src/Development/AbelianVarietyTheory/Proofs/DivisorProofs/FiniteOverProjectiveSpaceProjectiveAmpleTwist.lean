import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FiniteOverPSpace

theorem isProjOver_and_isAmpleLB : ∀ (o : Type) [CommRing o] [IsNoetherianRing o] (n k : ℕ) (Z : Scheme.{0}) (p : Z ⟶ PSpace o n), 1 ≤ k → IsFinite p → IsProjOver (p ≫ PSpace.str o n) ∧ (lbPow ((ProjSpace.O1 o n).pull p) k).IsLB ∧ IsAmpleLB (lbPow ((ProjSpace.O1 o n).pull p) k) ∧ ∀ (Y : Scheme.{0}) (h : Y ⟶ Z), LBIso ((lbPow ((ProjSpace.O1 o n).pull p) k).pull h) (lbPow ((ProjSpace.O1 o n).pull (h ≫ p)) k) := by
  intro o _ _ n k Z p hk hp
  have hO := ProjSpace.O1_isLB o n
  have hA : IsAmpleLB ((ProjSpace.O1 o n).pull p) := (isAmple_projective_O_one o n).pull_of_isAffineHom p
  refine ⟨isProjOver_comp_of_isFinite p ⟨n, 𝟙 _, inferInstance, Category.id_comp _⟩, isLB_lbPow hA.isLB k,
    (isAmpleLB_pow_iff hA.isLB hk).2 hA, fun Y h => ?_⟩
  refine (CechPic.cls_eq_iff (pull_isLB (isLB_lbPow hA.isLB k) h) (isLB_lbPow (pull_isLB hO (h ≫ p)) k)).1 ?_
  rw [CechPic.cls_pull (isLB_lbPow hA.isLB k), CechPic.cls_lbPow hA.isLB, CechPic.cls_lbPow (pull_isLB hO (h ≫ p)),
    CechPic.cls_pull hO, CechPic.cls_pull hO, CechPic.pull_comp, map_nsmul]

end GlobalTheory.FiniteOverPSpace

end
