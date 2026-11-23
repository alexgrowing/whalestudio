import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyValsSec

theorem gm_pull_g {X X' Y : Scheme.{0}} (L : LB X) (F : X' ⟶ X) (f : Y ⟶ X') (y : Y) (J J' : PUnit → L.ι)
    (hj : F (f y) ∈ L.U (J PUnit.unit)) (hj' : F (f y) ∈ L.U (J' PUnit.unit)) :
    gm f y ((L.pull F).U J ⊓ (L.pull F).U J') ((L.pull F).g J J') =
      gm (f ≫ F) y _ (L.g (J PUnit.unit) (J' PUnit.unit)) := by
  have hp : f y ∈ (L.pull F).U J ⊓ (L.pull F).U J' := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  show gm f y _ (∏ _k : PUnit, (res _ (pullU F _ (L.g (J PUnit.unit) (J' PUnit.unit)))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res f y _ hp _).trans (gm_pull f F y (L.U _ ⊓ L.U _) ⟨hj, hj'⟩ _)

theorem exists_sec_of_chart {X X' : Scheme.{0}} (A B : LB X) (hB : B.IsLB) (σ : (CechPic.tens A B).Sec) (b : B.ι)
    (F : X' ⟶ X) (hb : ∀ y : X', F y ∈ B.U b) :
    ∃ t : (A.pull F).Sec, ∀ (j : (A.pull F).ι)
      (h : (A.pull F).U j ≤ F ⁻¹ᵁ (CechPic.tens A B).U (j PUnit.unit, b)),
      t.f j = (F.appLE _ _ h).hom (σ.f (j PUnit.unit, b)) := by
  have hle : ∀ j : (A.pull F).ι, (A.pull F).U j ≤ F ⁻¹ᵁ (CechPic.tens A B).U (j PUnit.unit, b) :=
    fun j y hy => ⟨mem_pull.1 hy, hb y⟩
  refine ⟨⟨fun j => (F.appLE _ _ (hle j)).hom (σ.f (j PUnit.unit, b)), fun j j' => ?_⟩, fun _ _ => rfl⟩
  apply TopCat.Presheaf.section_ext X'.sheaf
  intro y hy
  have hy' : (𝟙 X' : X' ⟶ X') y ∈ (A.pull F).U j ⊓ (A.pull F).U j' := hy
  have hj : F y ∈ A.U (j PUnit.unit) := mem_pull.1 hy.1
  have hj' : F y ∈ A.U (j' PUnit.unit) := mem_pull.1 hy.2
  have hp : (𝟙 X' ≫ F) y ∈ (CechPic.tens A B).U (j PUnit.unit, b) := ⟨hj, hb y⟩
  have hq : (𝟙 X' ≫ F) y ∈ (CechPic.tens A B).U (j' PUnit.unit, b) := ⟨hj', hb y⟩
  have e := gs_compat σ (𝟙 X' ≫ F) y hp hq
  have e₁ := CechPic.gm_tens A B (𝟙 X' ≫ F) y (j PUnit.unit, b) (j' PUnit.unit, b) hp hq
  rw [gm_self hB (𝟙 X' ≫ F) y hp.2, _root_.mul_one] at e₁
  rw [e₁] at e
  refine (gs_eq (𝟙 X') y _ hy' _).symm.trans (Eq.trans ?_ (gs_eq (𝟙 X') y _ hy' _))
  refine (gs_res _ y _ hy' _).trans ((gs_appLE F _ _ _ (𝟙 X') y hy'.1 _).trans (e.trans ?_))
  refine Eq.trans ?_ (gs_mul _ y _ hy' _ _).symm
  refine congrArg₂ (· * ·) ?_ ((gs_res _ y _ hy' _).trans (gs_appLE F _ _ _ (𝟙 X') y hy'.2 _)).symm
  exact ((gs_unit _ y _ hy' _).trans (congrArg Units.val (gm_pull_g A F (𝟙 X') y j j' hj hj'))).symm

theorem exists_locSec : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec) (i : δ.ι) (R : Type) [CommRing R] (ξ : Sp R ⟶ S),
    δ.IsLB → ⊤ ≤ ξ ⁻¹ᵁ δ.U i → ∃ t : (KeyVals.bL L ξ).L.Sec, KeyVals.IsLocSec σ i ξ t := by
  intro S G _ _ L δ σ i R _ ξ hδ hξ
  refine exists_sec_of_chart L.L (δ.pull G.hom) (LB.isLB_pull hδ _) σ (fun _ => i) (pullback.fst G.hom ξ) fun y => ?_
  refine mem_pull.2 ?_
  have h : (pullback.fst G.hom ξ ≫ G.hom) y ∈ δ.U i := by
    rw [pullback.condition]
    exact hξ (Set.mem_univ (pullback.snd G.hom ξ y))
  exact h

end GlobalTheory.KeyValsSec

end
