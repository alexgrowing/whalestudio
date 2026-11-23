import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegCompData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitOfBasicOpenTop
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RescaleBoth

open GlobalTheory.ArcPull GlobalTheory.ArcQ GlobalTheory.RescaleLift
open GlobalTheory.PsiEvenPull (proj)

theorem isUnit_fnOn_of_le {R : Type} [CommRing R] {W : (Sp R).Opens} (r : R) (h : W ≤ (Sp R).basicOpen (fnSp R r)) :
    IsUnit (fnOn W r) := isUnit_of_basicOpen_top _ (by
  have e := Scheme.preimage_basicOpen W.ι (fnSp R r)
  refine Eq.trans e.symm (top_le_iff.1 fun x _ => h x.2))

theorem mem_basicOpen_of_ne {R F : Type} [CommRing R] [Field F] (α : R →+* F) {r : R} (h : α r ≠ 0) {Z : Scheme.{0}}
    (s : Z ⟶ Sp F) (z : Z) : (s ≫ spMap α) z ∈ (Sp R).basicOpen (fnSp R r) := by
  have hpre : (s ≫ spMap α) ⁻¹ᵁ (Sp R).basicOpen (fnSp R r) = ⊤ := by
    rw [Scheme.preimage_basicOpen]
    refine Scheme.basicOpen_of_isUnit _ ?_
    refine (congrArg IsUnit (appTop_comp_spMap α s r)).mpr ?_
    exact ((IsUnit.mk0 _ h).map (fnSp _)).map s.appTop.hom
  exact (show z ∈ (s ≫ spMap α) ⁻¹ᵁ (Sp R).basicOpen (fnSp R r) from hpre.ge trivial)

theorem val_psiOn_rescale {R F : Type} [CommRing R] [IsDomain R] [Field F] (Q : DegPre R) (g : Q.X → (FractionRing R)ˣ)
    {W W₀ : (Sp R).Opens} (ψ : PsiOn Q W) (ψ₀ : PsiOn (GlobalTheory.PolDeg.rescale Q g) W₀) (y : Q.X) (a b : R)
    (hab : (g y : FractionRing R) * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a)
    (α : R →+* F) (hb : α b ≠ 0) (v : Fˣ) (hv : (v : F) * α b = α a) {Z : Scheme.{0}} (r : Z ⟶ W.toScheme)
    (r₀ : Z ⟶ W₀.toScheme) (s : Z ⟶ Sp F) (hr : r ≫ W.ι = s ≫ spMap α) (hr₀ : r₀ ≫ W₀.ι = s ≫ spMap α)
    (z : Z) (J) (hJ : Good Q.P.L z J) :
    val (ψ₀.psi y) r₀ z J = gm s z ⊤ (unitOn v) * val (ψ.psi y) r z J := by
  have ha : α a ≠ 0 := hv ▸ mul_ne_zero v.ne_zero hb
  have ha' : algebraMap R (FractionRing R) a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 fun h => ha (by rw [h, map_zero])
  have hb' : algebraMap R (FractionRing R) b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 fun h => hb (by rw [h, map_zero])
  obtain ⟨W', l, l₀, la, lb, hm⟩ : ∃ W' : (Sp R).Opens, W' ≤ W ∧ W' ≤ W₀ ∧ W' ≤ (Sp R).basicOpen (fnSp R a) ∧
      W' ≤ (Sp R).basicOpen (fnSp R b) ∧ ∀ x, (s ≫ spMap α) x ∈ W' :=
    ⟨(W ⊓ W₀) ⊓ ((Sp R).basicOpen (fnSp R a) ⊓ (Sp R).basicOpen (fnSp R b)), inf_le_left.trans inf_le_left,
      inf_le_left.trans inf_le_right, inf_le_right.trans inf_le_left, inf_le_right.trans inf_le_right, fun x =>
      ⟨⟨(congrArg (fun q => q x ∈ W) hr).mp (r x).2, (congrArg (fun q => q x ∈ W₀) hr₀).mp (r₀ x).2⟩,
        mem_basicOpen_of_ne α ha s x, mem_basicOpen_of_ne α hb s x⟩⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Z ⟶ W'.toScheme, ρ ≫ W'.ι = s ≫ spMap α :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hm x), IsOpenImmersion.lift_fac _ _ _⟩
  let m : W'.toScheme ⟶ W.toScheme := (Sp R).homOfLE l
  let m₀ : W'.toScheme ⟶ W₀.toScheme := (Sp R).homOfLE l₀
  have f : m ≫ W.ι = W'.ι := Scheme.homOfLE_ι _ _
  have f₀ : m₀ ≫ W₀.ι = W'.ι := Scheme.homOfLE_ι _ _
  have ua := isUnit_fnOn_of_le a la
  have ub := isUnit_fnOn_of_le b lb
  have hφ : m ≫ (toUnit (TW W) ≫ Q.c y).left = m₀ ≫ (toUnit (TW W₀) ≫ Q.c y).left := by
    show m ≫ W.ι ≫ (Q.c y).left = m₀ ≫ W₀.ι ≫ (Q.c y).left
    rw [← Category.assoc, f, ← Category.assoc, f₀]
  have key := GlobalTheory.PsiEvenPull.val_eq_of_app_injective Q.P.isLB
    (u := GlobalTheory.UU.scaleGen ub.unit (LB.pullGen Q.P.L _ _ (ψ₀.psi y) m₀))
    (u' := GlobalTheory.UU.scaleGen ua.unit (LB.pullGen Q.P.L _ _ (ψ.psi y) m))
    (fun U _ k => Finset.prod_congr rfl fun _ _ => congrArg (fun q => k q ^ (-1 : ℤ)) hφ)
    (jK R ∣_ W') (GlobalTheory.PsiEvenPull.app_injective_generic W')
    (GlobalTheory.UU.scaleGen_isGen _ (DVR.pullGen_isGen _ _ _ _ (ψ₀.psi_gen y) m₀))
    (GlobalTheory.UU.scaleGen_isGen _ (DVR.pullGen_isGen _ _ _ _ (ψ.psi_gen y) m)) (fun x I hI => by
      have e : (jK R ∣_ W') ≫ W'.ι = (jK R ⁻¹ᵁ W').ι ≫ jK R := morphismRestrict_ι _ _
      have p := GlobalTheory.ArcSpecialise.psiOn_generic ψ y ((jK R ∣_ W') ≫ m) (jK R ⁻¹ᵁ W').ι
        (by rw [Category.assoc, f, e]) hI
      have p₀ := GlobalTheory.ArcSpecialise.psiOn_generic ψ₀ y ((jK R ∣_ W') ≫ m₀) (jK R ⁻¹ᵁ W').ι
        (by rw [Category.assoc, f₀, e]) hI
      have q : val ((GlobalTheory.PolDeg.rescale Q g).psi y) (jK R ⁻¹ᵁ W').ι x I =
          gm (jK R ⁻¹ᵁ W').ι x ⊤ (unitOn (g y)) * val (Q.psi y) (jK R ⁻¹ᵁ W').ι x I :=
        GlobalTheory.UU.val_scaleGen (unitOn (g y)) (Q.psi y) _ hI
      have ga := gm_fnOn W' (algebraMap R (FractionRing R)) _ _ e a ua.unit (Units.mk0 _ ha') ua.unit_spec rfl x
      have gb := gm_fnOn W' (algebraMap R (FractionRing R)) _ _ e b ub.unit (Units.mk0 _ hb') ub.unit_spec rfl x
      have w : unitOn (Units.mk0 _ ha') = unitOn (Units.mk0 _ hb') * unitOn (g y) :=
        (congrArg unitOn (Units.ext (hab.symm.trans (_root_.mul_comm _ _)))).trans (map_mul _ _ _)
      refine (GlobalTheory.UU.val_scaleGen _ _ _ hI).trans (Eq.trans ?_ (GlobalTheory.UU.val_scaleGen _ _ _ hI).symm)
      refine (congrArg₂ (· * ·) gb ((val_pull hI _ _ _).trans (p₀.trans q))).trans
        (Eq.trans ?_ (congrArg₂ (· * ·) ga ((val_pull hI _ _ _).trans p)).symm)
      rw [w, map_mul, _root_.mul_assoc]) Z ρ z J hJ
  have ga := gm_fnOn W' α _ _ hρ a ua.unit (Units.mk0 _ ha) ua.unit_spec rfl z
  have gb := gm_fnOn W' α _ _ hρ b ub.unit (Units.mk0 _ hb) ub.unit_spec rfl z
  have w : unitOn (Units.mk0 _ ha) = unitOn (Units.mk0 _ hb) * unitOn v :=
    (congrArg unitOn (Units.ext (hv.symm.trans (_root_.mul_comm _ _)))).trans (map_mul _ _ _)
  have c : ρ ≫ m = r := by rw [← cancel_mono W.ι, Category.assoc, f, hρ, hr]
  have c₀ : ρ ≫ m₀ = r₀ := by rw [← cancel_mono W₀.ι, Category.assoc, f₀, hρ, hr₀]
  have k₂ := (congrArg₂ (· * ·) gb (val_pull hJ _ _ _)).symm.trans ((GlobalTheory.UU.val_scaleGen _ _ _ hJ).symm.trans
    (key.trans ((GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans (congrArg₂ (· * ·) ga (val_pull hJ _ _ _)))))
  rw [w, map_mul, _root_.mul_assoc, c, c₀] at k₂
  exact mul_left_cancel k₂

theorem exists_isPullDeg_rescale : ∀ {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {θ : R →+* V} {Q : DegPre R} {Q' : DegPre V} (hD : IsPullDeg θ Q Q') (g : Q.X → (FractionRing R)ˣ) (g' : Q'.X → (FractionRing V)ˣ), Nonempty (PsiOn (GlobalTheory.PolDeg.rescale Q g) ⊤) → (∀ y, ∃ a b : R, θ b ≠ 0 ∧ (g (hD.xe y) : FractionRing R) * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a ∧ (g' y : FractionRing V) * algebraMap V (FractionRing V) (θ b) = algebraMap V (FractionRing V) (θ a)) → ∃ h : IsPullDeg θ (GlobalTheory.PolDeg.rescale Q g) (GlobalTheory.PolDeg.rescale Q' g'), h.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ) = hD.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ) ∧ ∀ y, h.xe y = hD.xe y := by
  intro R V _ _ _ _ θ Q Q' h g g' ⟨ψ₀⟩ H
  have hsq : jK V ≫ specOf θ = 𝟙 (TK V).left ≫ spMap ((algebraMap V (FractionRing V)).comp θ) := by
    rw [Category.id_comp]
    exact (Spec.map_comp (CommRingCat.ofHom θ) (CommRingCat.ofHom (algebraMap V (FractionRing V)))).symm
  obtain ⟨t, ht⟩ : ∃ t : (TK V).left ⟶ (TW (⊤ : (Sp R).Opens)).left, t ≫ (⊤ : (Sp R).Opens).ι = jK V ≫ specOf θ :=
    ⟨IsOpenImmersion.lift (⊤ : (Sp R).Opens).ι (jK V ≫ specOf θ) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  have gp : IsGrpPullback Q'.P.A Q.P.A (spMap θ) (proj h) := pull_grp h
  have hr : PMaps (K := PUnit) h.w (fun _ => eSec Q'.P.A) (fun _ => eSec Q.P.A) (fun _ => 1) Q'.rig Q.rig (spMap θ) :=
    GlobalTheory.FieldPull.pmaps_rig h
  have hc : ∀ x : Q'.X, (Q'.c x).left ≫ proj h = spMap θ ≫ (Q.c (h.xe x)).left := h.c_pr
  have hv : ∀ (x : Q'.X) (z : (TK V).left) J J', Good Q.P.L z J → Good Q'.P.L z J' →
      val (ψ₀.psi (h.xe x)) t z J =
        (om h.w z J J' (Q'.xK x))⁻¹ * val ((GlobalTheory.PolDeg.rescale Q' g').psi x) (𝟙 _) z J' := fun x z J J' hJ hJ' => by
    obtain ⟨a, b, hb, hab, hab'⟩ := H x
    have e0 := val_psiOn_rescale Q g h.psiW ψ₀ (h.xe x) a b hab ((algebraMap V (FractionRing V)).comp θ)
      ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hb) (g' x) hab' h.g t (𝟙 _)
      (h.g_comm.trans hsq) (ht.trans hsq) z J hJ
    have e1 := GlobalTheory.PsiEvenPull.psi_pull h x (𝟙 _) z hJ hJ'
    rw [Category.id_comp] at e1
    have e2 : val ((GlobalTheory.PolDeg.rescale Q' g').psi x) (𝟙 _) z J' =
        gm (𝟙 (TK V).left) z ⊤ (unitOn (g' x)) * val (Q'.psi x) (𝟙 _) z J' :=
      GlobalTheory.UU.val_scaleGen (unitOn (g' x)) (Q'.psi x) (𝟙 _) hJ'
    refine e0.trans ?_
    rw [e1, e2, mul_left_comm]
    simp only [om, Category.id_comp]
  obtain ⟨hD, h₁, h₂, -⟩ := GlobalTheory.PullDegCompData.exists_isPullDeg_of_valW (GlobalTheory.PolDeg.rescale Q g)
    (GlobalTheory.PolDeg.rescale Q' g') ψ₀ t ht gp h.w ((isGen_iff h.w).1 h.w_gen) hr h.xe hc hv
  exact ⟨hD, h₁, h₂⟩

end GlobalTheory.RescaleBoth
