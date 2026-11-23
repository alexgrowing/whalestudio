import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionSmoothAffineSurjectiveFourierTermsStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatSurjectiveKernel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mum

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

namespace Ext

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht GlobalTheory.TorusModel GlobalTheory.TorusExt GlobalTheory.Serre

theorem exists_torusPt {T : Over (Sp R)} (x : T ⟶ splitTorus (Sp R) D.X) : ∃ g : GtPt D T, g.b = 1 ∧
    ∀ (χ : D.X) (Z : Scheme.{0}) (r : Z ⟶ T.left) y J, Good D.P.L y J →
      (val (g.s χ) r y J).val = gs r y ⊤ ((coord x).hom (AddMonoidAlgebra.single χ 1)) := by
  let u : Multiplicative D.X →* Γ(T.left, ⊤) :=
    { toFun := fun χ => (coord x).hom (AddMonoidAlgebra.single χ.toAdd 1)
      map_one' := Diag.coord_single_zero x
      map_mul' := fun a b => Diag.coord_single_add x _ _ }
  let v : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (Y := T.left) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim) := fun χ =>
    ⟨fun _ => res le_top (u.toHomUnits (Multiplicative.ofAdd χ))⟩
  have hv : ∀ χ (Z : Scheme.{0}) (r : Z ⟶ T.left) y J, Good D.P.L y J →
      val (v χ) r y J = gm r y ⊤ (u.toHomUnits (Multiplicative.ofAdd χ)) := fun χ Z r y J hJ =>
    gm_res r y _ (hJ.mem PEmpty.elim r) _
  obtain ⟨g, hb, hg⟩ := exists_pt (1 : T ⟶ D.P.A) v (fun χ i j => by
      obtain rfl : i = j := funext fun k => k.elim
      have e : (LB.LinComb D.P.L (Y := T.left) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim).g i i = 1 := by
        dsimp only [LB.LinComb]
        erw [Fintype.prod_empty]
        rfl
      rw [e, _root_.one_mul])
    (fun χ U _ h => by
      rw [prod_pt, _root_.mul_one, Fintype.prod_empty, inv_mul_cancel, _root_.one_mul, mul_inv_cancel])
    (fun y J hJ => by rw [hv _ _ _ _ _ hJ, ofAdd_zero, map_one, map_one])
    (fun χ χ' y J hJ => by
      have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
      rw [C.face₃, _root_.mul_one, hv _ _ _ _ _ hJ, hv _ _ _ _ _ hJ, hv _ _ _ _ _ hJ, ofAdd_add, map_mul, map_mul])
  exact ⟨g, hb, fun χ Z r y J hJ => by
    rw [hg _ _ _ _ _ hJ, hv _ _ _ _ _ hJ]; exact (gs_unit r y ⊤ trivial _).symm⟩

variable (Y : Ext D)

theorem pt_b {T : Over (Sp R)} (x : T ⟶ Y.H) : (Y.Φ T x).b = x ≫ Y.q := by
  have h := ((isPull_iff _ _ _).1 (Y.rep.1 T Y.H x (𝟙 _))).1
  rwa [Category.comp_id] at h

def torI : splitTorus (Sp R) D.X ⟶ Y.H :=
  (Y.Φ _).symm (exists_torusPt (D := D) (𝟙 _)).choose

theorem torI_pt {T : Over (Sp R)} (x : T ⟶ splitTorus (Sp R) D.X) : (Y.Φ T (x ≫ Y.torI)).b = 1 ∧
    ∀ (χ : D.X) y J, Good D.P.L y J →
      (cv (Y.Φ T (x ≫ Y.torI)) χ y J).val = gs (𝟙 _) y ⊤ ((coord x).hom (AddMonoidAlgebra.single χ 1)) := by
  obtain ⟨h₁, h₂⟩ := (isPull_iff _ _ _).1 (Y.rep.1 T _ x Y.torI)
  obtain ⟨e₁, e₂⟩ := (exists_torusPt (D := D) (𝟙 _)).choose_spec
  have e : Y.Φ _ Y.torI = (exists_torusPt (D := D) (𝟙 _)).choose := Equiv.apply_symm_apply _ _
  rw [e] at h₁ h₂
  refine ⟨by rw [h₁, e₁, MonObj.comp_one], fun χ y J hJ => ?_⟩
  rw [h₂ χ y J hJ, e₂ χ _ _ y J hJ]
  conv_rhs => rw [← Category.comp_id x, coord_comp]
  exact (gs_eq x.left y ⊤ trivial _).trans (gs_eq (𝟙 _) y ⊤ trivial _).symm

theorem torI_q : Y.torI ≫ Y.q = 1 := by
  have h := (Y.torI_pt (𝟙 _)).1
  rwa [pt_b, Category.id_comp] at h

theorem isMonHom_torI : IsMonHom Y.torI :=
  isMonHom_of_mul _ fun T x x' => (Y.Φ T).injective <| by
    refine isAdd_unique ((TorusModel.isAdd_iff _ _ _).2 ⟨?_, fun χ y J hJ => Units.ext ?_⟩) (Y.rep.2 T _ _)
    · rw [(Y.torI_pt _).1, (Y.torI_pt _).1, (Y.torI_pt _).1, _root_.mul_one]
    · have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
      rw [(Y.torI_pt x').1, C.face₃, _root_.mul_one, Units.val_mul, (Y.torI_pt _).2 χ y J hJ, (Y.torI_pt _).2 χ y J hJ,
        (Y.torI_pt _).2 χ y J hJ]
      exact (congrArg (gs _ y ⊤) (Diag.coord_mul x x' χ)).trans (gs_mul (𝟙 _) y ⊤ trivial _ _)

theorem isKernel_torI : IsPullback Y.torI (toUnit _) Y.q η[D.P.A] := by
  have ex : ∀ {T : Over (Sp R)} y, ∃ J, Good D.P.L (Z := T.left) y J := fun y => by
    choose I hI using fun χ => exists_chart D.P.isLB ((χ : _ ⟶ D.P.A.left) y)
    exact ⟨I, hI⟩
  refine Diag.isPullback_toUnit_of_lift _ Y.torI_q (fun {T} a b h => Diag.hom_ext fun χ => fn_ext fun y _ => ?_)
    fun {T} x hx => ?_
  · obtain ⟨J, hJ⟩ := ex y
    exact ((Y.torI_pt a).2 χ y J hJ).symm.trans (h ▸ (Y.torI_pt b).2 χ y J hJ)
  · have hb : (Y.Φ T x).b = 1 := (Y.pt_b x).trans hx
    have hF : ∀ χ, FormEq (DegPre.gtφT D T (Y.Φ T x).b χ) DegPre.gtε (K' := PEmpty.{1}) PEmpty.elim PEmpty.elim :=
      fun χ U _ h => by
        rw [prod_pt, hb, _root_.mul_one, Fintype.prod_empty, inv_mul_cancel, _root_.one_mul, mul_inv_cancel]
    choose s _ vs using fun χ => exists_gen D.P.isLB (hF χ) _ ((Y.Φ T x).isGen χ)
    have le : (⊤ : T.left.Opens) ≤ LB.wchart D.P.L (K := PEmpty.{1}) PEmpty.elim PEmpty.elim :=
      fun _ _ => Set.mem_iInter.2 fun k => k.elim
    let u : D.X → Γ(T.left, ⊤)ˣ := fun χ => res le ((s χ).s PEmpty.elim)
    have hu : ∀ χ y J, Good D.P.L y J → gs (𝟙 _) y ⊤ (u χ).val = (cv (Y.Φ T x) χ y J).val := fun χ y J hJ =>
      (gs_unit _ y ⊤ trivial _).trans (congrArg Units.val ((gm_res _ y le trivial _).trans
        ((val_of (s χ) _ y J PEmpty.elim fun k => k.elim).symm.trans (vs χ _ _ y J hJ))))
    let g : Multiplicative D.X →* Γ(T.left, ⊤) :=
      { toFun := fun χ => (u χ.toAdd).val
        map_one' := fn_ext fun y _ => by
          obtain ⟨J, hJ⟩ := ex y
          refine (hu 0 y J hJ).trans ?_
          rw [cv_zero _ hJ, gs_eq _ y ⊤ trivial, map_one, map_one, Units.val_one]
        map_mul' := fun a b => fn_ext fun y _ => by
          obtain ⟨J, hJ⟩ := ex y
          have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
          have e := cv_add (Y.Φ T x) hJ a.toAdd b.toAdd
          rw [hb, C.face₃, _root_.mul_one] at e
          refine (hu _ y J hJ).trans (Eq.trans ?_ (gs_mul _ y ⊤ trivial _ _).symm)
          exact (congrArg Units.val e).trans (congrArg₂ (· * ·) (hu _ y J hJ) (hu _ y J hJ)).symm }
    refine ⟨Diag.ofChar T g, (Y.Φ T).injective (pt_ext ((Y.torI_pt _).1.trans hb.symm) fun χ y J hJ => Units.ext ?_)⟩
    exact ((Y.torI_pt _).2 χ y J hJ).trans ((congrArg (gs _ y ⊤) (Diag.coord_ofChar T g χ)).trans (hu χ y J hJ))

theorem cv_torI {Z : Over (Sp R)} (t : Z ⟶ splitTorus (Sp R) D.X) (χ : D.X) (z : Z.left) J (hJ : Good D.P.L z J) :
    cv (Y.Φ Z (t ≫ Y.torI)) χ z J = gm t.left z ⊤ (charUnit (Sp R) D.X χ) := by
  have hc : t.left.appTop.hom (charUnit (Sp R) D.X χ).val = (coord t).hom (AddMonoidAlgebra.single χ 1) := by
    rw [GlobalTheory.SplitTorus.charUnit_val]
    conv_rhs => rw [← Category.comp_id t, coord_comp]
    rfl
  refine Units.ext (((Y.torI_pt t).2 χ z J hJ).trans ?_)
  rw [← gs_unit t.left z ⊤ trivial, ← hc]
  exact (gs_eq (𝟙 _) z ⊤ trivial _).trans (gs_eq t.left z ⊤ trivial _).symm

theorem cv_torI_mul {Z : Over (Sp R)} (t : Z ⟶ splitTorus (Sp R) D.X) (g : Z ⟶ Y.H) (χ : D.X) (z : Z.left) J
    (hJ : Good D.P.L z J) :
    cv (Y.Φ Z ((t ≫ Y.torI) * g)) χ z J = gm t.left z ⊤ (charUnit (Sp R) D.X χ) * cv (Y.Φ Z g) χ z J := by
  have h := ((TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 Z (t ≫ Y.torI) g)).2 χ z J hJ
  have C : IsCub (th D (T := Z) z J) := isCub_cubV D.cub hJ
  rw [(Y.torI_pt t).1, C.face₂, _root_.mul_one, Y.cv_torI t χ z J hJ] at h
  exact h

end Ext

theorem ext_torus : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D), ∃ i : splitTorus (Sp R) D.X ⟶ Y.H,
    IsMonHom i ∧ IsPullback i (toUnit _) Y.q η[D.P.A] ∧ ∀ (χ : D.X) (Z : Over (Sp R)) (t : Z ⟶ splitTorus (Sp R) D.X)
      (g : Z ⟶ Y.H) (z : Z.left) J, Good D.P.L z J →
        val ((Y.Φ Z ((t ≫ i) * g)).s χ) (𝟙 _) z J = gm t.left z ⊤ (charUnit (Sp R) D.X χ) * val ((Y.Φ Z g).s χ) (𝟙 _) z J :=
  fun _ _ _ _ Y => ⟨Y.torI, Y.isMonHom_torI, Y.isKernel_torI, fun χ _ t g z J hJ => Y.cv_torI_mul t g χ z J hJ⟩

end GlobalTheory.Mum
