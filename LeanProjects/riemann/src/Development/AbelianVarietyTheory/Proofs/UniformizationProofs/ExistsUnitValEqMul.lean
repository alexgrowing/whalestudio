import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem exists_unit_val_eq_mul {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ c : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J).val = gs r z ⊤ c.val * (val u' r z J).val := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  rw [← Units.mul_inv_eq_iff_eq_mul, ← Units.val_mul, ← val_inv, ← val_mul hJ, ← hv Z r z J hJ,
    val_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans (gs_unit r z ⊤ trivial _).symm

theorem exists_psiScal : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V), ∃ (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing V)ˣ), PsiScal D ga a := by
  intro V _ _ _ D
  choose ga hga using fun χ : D.X =>
    DVR.exists_gen_of_local (V := V) D.P.L D.P.isLB (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)
  have key := fun χ : D.X => exists_unit_val_eq_mul D.P.isLB (D.psi_gen χ)
    (DVR.pullGen_isGen D.P.L _ _ (ga χ) (hga χ) (toUnit (TK V)).left)
  choose c hc using key
  refine ⟨ga, fun χ => Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).hom.hom.toMonoidHom (c χ),
    fun χ => ⟨hga χ, fun T κ z J hJ => ?_⟩⟩
  have e : κ.left ≫ (toUnit (TK V)).left = (toUnit T).left := by
    rw [← Over.comp_left, comp_toUnit]
  refine (hc χ T.left κ.left z J hJ).trans ?_
  refine congrArg₂ (· * ·) ?_ (congrArg Units.val ((val_pull hJ (ga χ) _ κ.left).trans (by rw [e])))
  have e₂ : scal κ.left ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).hom.hom (c χ).val) =
      κ.left.appTop.hom (c χ).val :=
    congrArg κ.left.appTop.hom (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))) _)
  refine Eq.trans ?_ (congrArg (gs (𝟙 _) z ⊤) e₂).symm
  exact (congrArg (fun q => gs q z ⊤ (c χ).val) (Category.id_comp κ.left)).symm.trans
    (gs_pull (𝟙 _) κ.left z ⊤ trivial _).symm

end GlobalTheory
