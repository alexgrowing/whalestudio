import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullCubicalOfGenericOfExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsGenericRigidifiedGeneratorToricChartPowerStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartCubExt

theorem cube_pull_of_chart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {k : Type} [Field k] {m n : ℕ} (tC : SAB H (Sp (ChartRing k m n))) {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (ξ : Sp (ChartRing k m n) ⟶ S) (πC : tC.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tC.G G ξ πC → ∀ (PP : RigLB G) (cub : CubicalStr G PP) {X' : Scheme.{0}} (tF : SAB H X') (j : X' ⟶ S) (e : tF.G.left ⟶ G.left) (cm : CubeMap tF.G G), cm.F = e → cm.e = j → cm.IsPullCubical tF.cub cub → ∀ (y : Sp (FractionRing (ChartRing k m n)) ⟶ X'), y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK tC (jK _)) (b : SABMap tK tF y), a.φ ≫ πC = b.φ ≫ e → ∃ cm' : CubeMap tC.G G, cm'.F = πC ∧ cm'.e = ξ ∧ cm'.IsPullCubical tC.cub cub := by
  intro E _ _ _ H k _ m n tC S G _ _ ξ πC hG hπ PP cub X' tF j e cm hcF hce hcm y hy tK a b hab
  refine ⟨cubeMapOf hπ, rfl, rfl, ?_⟩
  let c2 : CubeMap tK.G G :=
    { F := b.cm.F ≫ cm.F, F3 := b.cm.F3 ≫ cm.F3, e := b.cm.e ≫ cm.e
      e_comm := by rw [← Category.assoc, b.cm.e_comm, Category.assoc, cm.e_comm, Category.assoc]
      psum_comm := fun I => by
        rw [← Category.assoc, b.cm.psum_comm, Category.assoc, cm.psum_comm, Category.assoc] }
  let c3 : CubeMap tK.G G :=
    { F := a.cm.F ≫ (cubeMapOf hπ).F, F3 := a.cm.F3 ≫ (cubeMapOf hπ).F3, e := a.cm.e ≫ (cubeMapOf hπ).e
      e_comm := by rw [← Category.assoc, a.cm.e_comm, Category.assoc, (cubeMapOf hπ).e_comm, Category.assoc]
      psum_comm := fun I => by
        rw [← Category.assoc, a.cm.psum_comm, Category.assoc, (cubeMapOf hπ).psum_comm, Category.assoc] }
  have H2 : c2.IsPullCubical tK.cub cub :=
    pullCubComp _ _ _ _ _ _ cm b.cm c2 _ _ _ _ _ _ rfl rfl rfl hcm b.lin
  have h₁ : c2.F = a.cm.F ≫ (cubeMapOf hπ).F := by
    show b.cm.F ≫ cm.F = a.cm.F ≫ πC
    rw [hcF]; exact hab.symm
  have h₂ : c2.F3 = a.cm.F3 ≫ (cubeMapOf hπ).F3 := by
    show c2.F3 = c3.F3
    refine hom_ext_triple _ fun i => ?_
    rw [cubeMap_comp_proj_three c2 i, cubeMap_comp_proj_three c3 i]
    exact congrArg (fun z => (x3 tK.G i).left ≫ z) h₁
  have h₃ : c2.e = a.cm.e ≫ (cubeMapOf hπ).e := by
    show b.cm.e ≫ cm.e = a.cm.e ≫ ξ
    rw [b.base, hce, a.base, hy]
  exact GlobalTheory.ChartCubExt.isPullCubical_of_generic_of_ext (GlobalTheory.T.extendsGenericRigidifiedGenerator_toricChartPowerSeriesRing k m n) tC.semi cub tC.cub tK.cub
    (cubeMapOf hπ) a.cm c2 a.cart.1 a.base h₁ h₂ h₃ a.lin H2

end GlobalTheory.ChartCubExt
