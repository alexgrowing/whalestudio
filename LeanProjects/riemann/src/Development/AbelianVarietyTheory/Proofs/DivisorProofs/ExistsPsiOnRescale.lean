import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegCompData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitOfBasicOpenTop
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PullDegResc

open GlobalTheory.ArcPull GlobalTheory.ArcQ GlobalTheory.RescaleLift
open GlobalTheory.PsiEvenPull (proj)

theorem isUnit_fnOn_le {R₀ : Type} [CommRing R₀] (f r : R₀) (N : ℕ) (hr : r ∣ f ^ N) {W : (Sp R₀).Opens}
    (hle : W ≤ (Sp R₀).basicOpen (fnSp R₀ f)) : IsUnit (fnOn W r) := by
  have e := appTop_fnOn ((Sp R₀).basicOpen (fnSp R₀ f)) (RingHom.id R₀) ((Sp R₀).homOfLE hle) W.ι (by
    rw [Scheme.homOfLE_ι]
    exact (Category.comp_id _).symm.trans (congrArg (W.ι ≫ ·) (Spec.map_id _).symm)) r
  have := (isUnit_fnOn f r N hr).map ((Sp R₀).homOfLE hle).appTop.hom
  rw [e] at this
  exact this

theorem gm_mono {R₀ K : Type} [CommRing R₀] [Field K] (W : (Sp R₀).Opens) (α : R₀ →+* K) {Z : Scheme.{0}}
    (t : Z ⟶ W.toScheme) (s : Z ⟶ Sp K) (h : t ≫ W.ι = s ≫ spMap α) {I : Type} [Fintype I] (a : I → R₀)
    (ha : ∀ k, IsUnit (fnOn W (a k))) (h0 : ∀ k, α (a k) ≠ 0) (n : I → ℤ) (v : Kˣ)
    (hv : (v : K) = ∏ k, α (a k) ^ n k) (z : Z) :
    gm t z ⊤ (∏ k, (ha k).unit ^ n k) = gm s z ⊤ (unitOn v) := by
  obtain rfl : v = ∏ k, Units.mk0 (α (a k)) (h0 k) ^ n k := Units.ext (by
    rw [hv]; simp)
  show _ = GlobalTheory.TauTwist.unitAt s z _
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow, map_zpow]
  exact congrArg (· ^ n k) (gm_fnOn W α t s h (a k) _ _ (ha k).unit_spec rfl z)

theorem exists_psiOn_rescale {R₀ : Type} [CommRing R₀] [IsDomain R₀] (D₁ : DegPre R₀) (κ₀ : D₁.X → (FractionRing R₀)ˣ)
    {W W' : (Sp R₀).Opens} (ψ : PsiOn D₁ W) (hle : W' ≤ W) (u : D₁.X → Γ(W'.toScheme, ⊤)ˣ)
    (hu : ∀ (y : D₁.X) {Z : Scheme.{0}} (t : Z ⟶ W'.toScheme) (s : Z ⟶ (TK R₀).left), t ≫ W'.ι = s ≫ jK R₀ → ∀ z,
      gm t z ⊤ (u y) = gm s z ⊤ (unitOn (κ₀ y))) :
    ∃ ψW : PsiOn (GlobalTheory.PolDeg.rescale D₁ κ₀) W', ∀ (y : D₁.X) {Z : Scheme.{0}} (t : Z ⟶ W'.toScheme) (z : Z) J,
      Good D₁.P.L z J → val (ψW.psi y) t z J = gm t z ⊤ (u y) * val (ψ.psi y) (t ≫ (Sp R₀).homOfLE hle) z J := by
  let m : W'.toScheme ⟶ W.toScheme := (Sp R₀).homOfLE hle
  have hm : m ≫ W.ι = W'.ι := Scheme.homOfLE_ι _ _
  have hφ : ∀ y : D₁.X, m ≫ (toUnit (TW W) ≫ D₁.c y).left = (toUnit (TW W') ≫ D₁.c y).left := fun y => by
    show m ≫ W.ι ≫ (D₁.c y).left = W'.ι ≫ (D₁.c y).left
    rw [← Category.assoc, hm]
  choose b hb vb using fun y : D₁.X => exists_gen D₁.P.isLB (K' := PUnit)
    (φ' := fun _ => (toUnit (TW W') ≫ D₁.c y).left) (ε' := fun _ => -1)
    (fun U _ k => Finset.prod_congr rfl fun _ _ => congrArg (fun q => k q ^ (-1 : ℤ)) (hφ y))
    (GlobalTheory.UU.scaleGen (u y) (LB.pullGen D₁.P.L _ _ (ψ.psi y) m))
    (GlobalTheory.UU.scaleGen_isGen _ (DVR.pullGen_isGen _ _ _ _ (ψ.psi_gen y) m))
  have ev : ∀ (y : D₁.X) {Z : Scheme.{0}} (t : Z ⟶ W'.toScheme) (z : Z) J, Good D₁.P.L z J →
      val (b y) t z J = gm t z ⊤ (u y) * val (ψ.psi y) (t ≫ m) z J := fun y Z t z J hJ =>
    (vb y Z t z J hJ).trans ((GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _)))
  refine ⟨{ psi := b, psi_gen := hb, psi_eq := fun y => corr_of_val D₁.P.isLB fun z J hJ => ?_ }, ev⟩
  refine (val_pull hJ _ _ _).trans ((ev y _ z J hJ).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))
  refine (congrArg₂ (· * ·) ?_ ?_).trans (GlobalTheory.UU.val_scaleGen (unitOn (κ₀ y)) (D₁.psi y) _ hJ).symm
  · refine hu y _ _ ?_ z
    rw [Category.id_comp, Category.id_comp, morphismRestrict_ι]
  · refine GlobalTheory.ArcSpecialise.psiOn_generic ψ y _ _ ?_ hJ
    rw [Category.assoc, hm, Category.id_comp, Category.id_comp, morphismRestrict_ι]

theorem exists_rescale {R₀ R : Type} [CommRing R₀] [IsDomain R₀] [CommRing R] [IsDomain R] {φ : R₀ →+* R}
    {D₁ : DegPre R₀} {D : DegPre R} (h : IsPullDeg φ D₁ D) (κ₀ : D₁.X → (FractionRing R₀)ˣ)
    (κ : D.X → (FractionRing R)ˣ) {I : Type} [Fintype I] (s : I → R₀) (hs : ∀ k, φ (s k) ≠ 0) (n : D₁.X → I → ℤ)
    (h₀ : ∀ y, (κ₀ y : FractionRing R₀) = ∏ k, algebraMap R₀ (FractionRing R₀) (s k) ^ n y k)
    (h₁ : ∀ x, (κ x : FractionRing R) = ∏ k, algebraMap R (FractionRing R) (φ (s k)) ^ n (h.xe x) k) :
    ∃ h' : IsPullDeg φ (GlobalTheory.PolDeg.rescale D₁ κ₀) (GlobalTheory.PolDeg.rescale D κ), proj h' = proj h ∧ ∀ x, h'.xe x = h.xe x := by
  classical
  have hf : φ (∏ k, s k) ≠ 0 := by
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun k _ => hs k
  set f := ∏ k, s k with hfd
  set W' : (Sp R₀).Opens := h.W ⊓ (Sp R₀).basicOpen (fnSp R₀ f) with hW'
  have hsq : jK R ≫ specOf φ = 𝟙 (TK R).left ≫ spMap ((algebraMap R (FractionRing R)).comp φ) := by
    rw [Category.id_comp]
    exact (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom (algebraMap R (FractionRing R)))).symm
  have hpre : (jK R ≫ specOf φ) ⁻¹ᵁ (Sp R₀).basicOpen (fnSp R₀ f) = ⊤ := by
    rw [Scheme.preimage_basicOpen]
    refine Scheme.basicOpen_of_isUnit _ ?_
    rw [hsq]
    refine (congrArg IsUnit (appTop_comp_spMap ((algebraMap R (FractionRing R)).comp φ) (𝟙 _) f)).mpr ?_
    exact ((IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hf)).map (fnSp _)).map
      (Scheme.Hom.appTop (𝟙 (Sp (FractionRing R)))).hom
  obtain ⟨g, hg⟩ : ∃ g : (TK R).left ⟶ (TW W').left, g ≫ W'.ι = jK R ≫ specOf φ :=
    ⟨IsOpenImmersion.lift W'.ι (jK R ≫ specOf φ) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      refine ⟨?_, (show y ∈ (jK R ≫ specOf φ) ⁻¹ᵁ (Sp R₀).basicOpen (fnSp R₀ f) from hpre.ge trivial)⟩
      rw [← h.g_comm]
      exact (h.g y).2), IsOpenImmersion.lift_fac _ _ _⟩
  have hle : W' ≤ h.W := inf_le_left
  have hU : ∀ k, IsUnit (fnOn W' (s k)) := fun k =>
    isUnit_fnOn_le f _ 1 (by rw [pow_one]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ k)) inf_le_right
  have s0 : ∀ k, algebraMap R₀ (FractionRing R₀) (s k) ≠ 0 := fun k =>
    (map_ne_zero_iff _ (IsFractionRing.injective R₀ _)).2 fun e => hs k (by rw [e, map_zero])
  obtain ⟨ψW, hψW⟩ := exists_psiOn_rescale D₁ κ₀ h.psiW hle (fun y => ∏ k, (hU k).unit ^ n y k)
    (fun y Z t r e z => gm_mono W' (algebraMap R₀ (FractionRing R₀)) t r e s hU s0 (n y) _ (h₀ y) z)
  have hgm : g ≫ (Sp R₀).homOfLE hle = h.g := by
    rw [← cancel_mono h.W.ι, Category.assoc, Scheme.homOfLE_ι, hg, h.g_comm]
  have hv : ∀ (x : D.X) (z : (TK R).left) J J', Good D₁.P.L z J → Good D.P.L z J' →
      val (ψW.psi (h.xe x)) g z J = (om h.w z J J' (D.xK x))⁻¹ * val ((GlobalTheory.PolDeg.rescale D κ).psi x) (𝟙 _) z J' :=
    fun x z J J' hJ hJ' => by
    rw [hψW _ g z J hJ, hgm]
    have e1 := GlobalTheory.PsiEvenPull.psi_pull h x (𝟙 _) z hJ hJ'
    rw [Category.id_comp] at e1
    have e2 : val ((GlobalTheory.PolDeg.rescale D κ).psi x) (𝟙 _) z J' =
        gm (𝟙 (TK R).left) z ⊤ (unitOn (κ x)) * val (D.psi x) (𝟙 _) z J' :=
      GlobalTheory.UU.val_scaleGen (unitOn (κ x)) (D.psi x) (𝟙 _) hJ'
    have e3 := gm_mono W' ((algebraMap R (FractionRing R)).comp φ) g (𝟙 _) (by rw [hg, hsq]) s hU
      (fun k => (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 (hs k)) (n (h.xe x)) (κ x) (h₁ x) z
    rw [e3, e1, e2, mul_left_comm]
    simp only [om, Category.id_comp]
  have gp : IsGrpPullback D.P.A D₁.P.A (spMap φ) (proj h) := pull_grp h
  have hr : PMaps (K := PUnit) h.w (fun _ => eSec D.P.A) (fun _ => eSec D₁.P.A) (fun _ => 1) D.rig D₁.rig (spMap φ) :=
    GlobalTheory.FieldPull.pmaps_rig h
  have hc : ∀ x : D.X, (D.c x).left ≫ proj h = spMap φ ≫ (D₁.c (h.xe x)).left := h.c_pr
  have hw : PGen h.w := (isGen_iff h.w).1 h.w_gen
  obtain ⟨hD, k₁, k₂, -⟩ := GlobalTheory.PullDegCompData.exists_isPullDeg_of_valW (GlobalTheory.PolDeg.rescale D₁ κ₀)
    (GlobalTheory.PolDeg.rescale D κ) ψW g hg gp h.w hw hr h.xe hc hv
  exact ⟨hD, k₁, k₂⟩

theorem rescale_inv {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (g : D.X → (FractionRing R)ˣ) (x : D.X) :
    (GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D g) fun y => (g y)⁻¹).psi x = D.psi x :=
  GlobalTheory.TorusExt.gen_ext_val D.P.isLB ((GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D g) fun y => (g y)⁻¹).psi_gen x)
    (D.psi_gen x) fun y J hJ => by
      refine (GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans ((congrArg₂ (· * ·) rfl (GlobalTheory.UU.val_scaleGen _ _ _ hJ)).trans ?_)
      show GlobalTheory.TauTwist.unitAt _ y (g x)⁻¹ * (GlobalTheory.TauTwist.unitAt _ y (g x) * _) = _
      rw [map_inv, inv_mul_cancel_left]

theorem exists_withPsi {R₀ R : Type} [CommRing R₀] [IsDomain R₀] [CommRing R] [IsDomain R] {φ : R₀ →+* R}
    {D₁ : DegPre R₀} {D : DegPre R} (h : IsPullDeg φ D₁ D) (ψ₁ : GlobalTheory.TauTwist.PsiFam D₁) (g₁ : ∀ χ, (ψ₁ χ).IsGen)
    (ψ : GlobalTheory.TauTwist.PsiFam D) (g : ∀ χ, (ψ χ).IsGen) (e₁ : D₁.psi = ψ₁) (e : D.psi = ψ) :
    ∃ h' : IsPullDeg φ (GlobalTheory.TauTwist.withPsi D₁ ψ₁ g₁) (GlobalTheory.TauTwist.withPsi D ψ g),
      proj h' = proj h ∧ ∀ x, h'.xe x = h.xe x := by
  subst e₁ e
  exact ⟨h, rfl, fun _ => rfl⟩

theorem exists_unscale {R₀ R : Type} [CommRing R₀] [IsDomain R₀] [CommRing R] [IsDomain R] {φ : R₀ →+* R}
    {D₁ : DegPre R₀} {D : DegPre R} (κ₀ : D₁.X → (FractionRing R₀)ˣ) (κ : D.X → (FractionRing R)ˣ)
    (h : IsPullDeg φ (GlobalTheory.PolDeg.rescale D₁ κ₀) (GlobalTheory.PolDeg.rescale D κ)) {I : Type} [Fintype I] (s : I → R₀)
    (hs : ∀ k, φ (s k) ≠ 0) (n : D₁.X → I → ℤ)
    (h₀ : ∀ y, (((κ₀ y)⁻¹ : (FractionRing R₀)ˣ) : FractionRing R₀) = ∏ k, algebraMap R₀ (FractionRing R₀) (s k) ^ n y k)
    (h₁ : ∀ x, (((κ x)⁻¹ : (FractionRing R)ˣ) : FractionRing R) =
      ∏ k, algebraMap R (FractionRing R) (φ (s k)) ^ n (h.xe x) k) :
    ∃ h' : IsPullDeg φ D₁ D, proj h' = proj h ∧ ∀ x, h'.xe x = h.xe x := by
  obtain ⟨h₂, a₁, a₂⟩ := exists_rescale h (fun y => (κ₀ y)⁻¹) (fun y => (κ y)⁻¹) s hs n h₀ h₁
  obtain ⟨h₃, b₁, b₂⟩ := exists_withPsi h₂ D₁.psi D₁.psi_gen D.psi D.psi_gen (funext (rescale_inv D₁ κ₀))
    (funext (rescale_inv D κ))
  exact ⟨h₃, b₁.trans a₁, fun x => (b₂ x).trans (a₂ x)⟩

theorem exists_rescale_inv {R₀ R : Type} [CommRing R₀] [IsDomain R₀] [CommRing R] [IsDomain R] {φ : R₀ →+* R}
    {D₁ : DegPre R₀} {D : DegPre R} (h : IsPullDeg φ D₁ D) (κ : D.X → (FractionRing R)ˣ) :
    ∃ h' : IsPullDeg φ D₁ (GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D κ) fun y => (κ y)⁻¹),
      proj h' = proj h ∧ ∀ x, h'.xe x = h.xe x :=
  exists_withPsi h D₁.psi D₁.psi_gen _ ((GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D κ) fun y => (κ y)⁻¹).psi_gen) rfl
    (funext (rescale_inv D κ)).symm

theorem main : (∀ {R₀ R : Type} [CommRing R₀] [IsDomain R₀] [CommRing R] [IsDomain R] {φ : R₀ →+* R} {D₁ : DegPre R₀} {D : DegPre R} (h : IsPullDeg φ D₁ D) (κ₀ : D₁.X → (FractionRing R₀)ˣ) (κ : D.X → (FractionRing R)ˣ) {I : Type} [Fintype I] (s : I → R₀), (∀ k, φ (s k) ≠ 0) → ∀ n : D₁.X → I → ℤ, (∀ y, (κ₀ y : FractionRing R₀) = ∏ k, algebraMap R₀ (FractionRing R₀) (s k) ^ n y k) → (∀ x, (κ x : FractionRing R) = ∏ k, algebraMap R (FractionRing R) (φ (s k)) ^ n (h.xe x) k) → ∃ h' : IsPullDeg φ (GlobalTheory.PolDeg.rescale D₁ κ₀) (GlobalTheory.PolDeg.rescale D κ), h'.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf φ) = h.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf φ) ∧ ∀ x, h'.xe x = h.xe x) ∧ (∀ {R₀ R : Type} [CommRing R₀] [IsDomain R₀] [CommRing R] [IsDomain R] {φ : R₀ →+* R} {D₁ : DegPre R₀} {D : DegPre R} (κ₀ : D₁.X → (FractionRing R₀)ˣ) (κ : D.X → (FractionRing R)ˣ) (h : IsPullDeg φ (GlobalTheory.PolDeg.rescale D₁ κ₀) (GlobalTheory.PolDeg.rescale D κ)) {I : Type} [Fintype I] (s : I → R₀), (∀ k, φ (s k) ≠ 0) → ∀ n : D₁.X → I → ℤ, (∀ y, (((κ₀ y)⁻¹ : (FractionRing R₀)ˣ) : FractionRing R₀) = ∏ k, algebraMap R₀ (FractionRing R₀) (s k) ^ n y k) → (∀ x, (((κ x)⁻¹ : (FractionRing R)ˣ) : FractionRing R) = ∏ k, algebraMap R (FractionRing R) (φ (s k)) ^ n (h.xe x) k) → ∃ h' : IsPullDeg φ D₁ D, h'.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf φ) = h.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf φ) ∧ ∀ x, h'.xe x = h.xe x) ∧ (∀ {R₀ R : Type} [CommRing R₀] [IsDomain R₀] [CommRing R] [IsDomain R] {φ : R₀ →+* R} {D₁ : DegPre R₀} {D : DegPre R} (h : IsPullDeg φ D₁ D) (κ : D.X → (FractionRing R)ˣ), ∃ h' : IsPullDeg φ D₁ (GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D κ) fun y => (κ y)⁻¹), h'.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf φ) = h.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf φ) ∧ ∀ x, h'.xe x = h.xe x) :=
  ⟨fun h κ₀ κ _ _ s hs n h₀ h₁ => exists_rescale h κ₀ κ s hs n h₀ h₁,
    fun κ₀ κ h _ _ s hs n h₀ h₁ => exists_unscale κ₀ κ h s hs n h₀ h₁, fun h κ => exists_rescale_inv h κ⟩

end GlobalTheory.PullDegResc
