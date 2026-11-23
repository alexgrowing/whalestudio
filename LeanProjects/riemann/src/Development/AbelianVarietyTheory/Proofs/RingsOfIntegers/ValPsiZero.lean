import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PsiZero

theorem cPoint_zero' {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) :
    cP D T 0 = 1 := by
  have := cPoint_add D T 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem val_psi_zero {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {z : (TK R).left}
    {J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) :
    val (D.psi 0) (𝟙 _) z J = (val D.rig (jK R) z J)⁻¹ := by
  have C : IsCub (th D (T := TK R) z J) := isCub_cubV D.cub hJ
  have vτ : ∀ a b : D.X, val (D.tau a b) (𝟙 _) z J =
      val (D.psi (a + b)) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ * (val (D.psi b) (𝟙 _) z J)⁻¹ *
        (val D.rigK (𝟙 _) z J)⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  have vρ : val D.rigK (𝟙 _) z J = val D.rig (jK R) z J := by
    refine (val_pull hJ _ _ _).trans ?_
    rw [Category.id_comp]
    rfl
  have vc : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 0 0 0)) (𝟙 _) z J = 1 := by
    refine (val_cub D.cub (𝟙 (TK R)) hJ (cP D _ 0) (cP D _ 0) (cP D _ 0)).trans ?_
    rw [Category.id_comp, cPoint_zero']
    exact C.face _ _
  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB 0 0 0) (𝟙 _)).trans (val_mul hJ _ _ _))
  have hp : ∀ a : D.X, a = 0 → val (D.psi a) (𝟙 _) z J = val (D.psi 0) (𝟙 _) z J := by
    rintro a rfl; rfl
  rw [vc, vτ, vτ, vρ, hp (0 + 0 + 0) (by simp), hp (0 + 0) (by simp), _root_.mul_one, mul_inv_cancel,
    _root_.one_mul] at e
  have e' := mul_eq_left.1 e.symm
  rw [← mul_inv, inv_eq_one] at e'
  exact eq_inv_of_mul_eq_one_left e'

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), (D.TauBimult → D.PsiIn 0 ⊤) ∧ ∀ (χ : D.X) (J J' : Ideal R), J ≤ J' → D.PsiIn χ J → D.PsiIn χ J' := by
  intro R _ _ D
  refine ⟨fun hB j V hV hle h => ?_, fun χ J J' hJ H j V hV hle h => ?_⟩
  · have c0 : (D.c 0).left = eSec D.P.A := by
      have := cPoint_zero' D (𝟙_ _)
      rw [cP, toUnit_unit, Category.id_comp, Hom.one_def, toUnit_unit, Category.id_comp] at this
      rw [this]; rfl
    have hx : D.xK 0 = jK R ≫ eSec D.P.A := by rw [← c0]; rfl
    have hle' : V ≤ LB.wchart D.P.L (K := PUnit) (fun _ => eSec D.P.A) j := fun y hy =>
      Set.mem_iInter.2 fun _ => by rw [← c0]; exact hle hy
    refine ⟨((Spec (CommRingCat.of R)).presheaf.map (homOfLE hle').op).hom (D.rig.s j)⁻¹.val,
      by rw [Ideal.map_top]; trivial, fn_ext fun y hy => ?_⟩
    have hy' : jK R y ∈ V := hy
    obtain ⟨J, hJ, eJ⟩ := exists_good D.P.L D.P.isLB y (K := PUnit) (fun _ => D.xK 0) j (fun _ _ _ => rfl)
      (fun k => Set.mem_iInter.1 (h hy) k)
    have e := val_psi_zero hB hJ
    rw [val_of (D.psi 0) _ y J j (fun k => (congrArg J (Category.id_comp (D.xK 0))).trans (eJ k)),
      val_of D.rig _ y J j (fun k => (congrArg J hx.symm).trans (eJ k))] at e
    refine (gs_pull (𝟙 _) (jK R) y V hy' _).trans (Eq.trans ?_
      ((gs_res (𝟙 _) y h hy _).trans (gs_unit _ _ _ (h hy) _)).symm)
    rw [Category.id_comp]
    refine (gs_res (jK R) y hle' hy' _).trans ((gs_unit _ _ _ (hle' hy') _).trans ?_)
    exact congrArg Units.val ((map_inv _ _).trans e.symm)
  · obtain ⟨r, hr, e⟩ := H j V hV hle h
    exact ⟨r, Ideal.map_mono hJ hr, e⟩

end GlobalTheory.PsiZero
