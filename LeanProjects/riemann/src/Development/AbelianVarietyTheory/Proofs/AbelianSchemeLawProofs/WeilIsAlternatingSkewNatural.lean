import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CommPairing

theorem val_div_eq {X Y S₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (p : Y ⟶ S₀) (hp : Function.Surjective p.appTop.hom)
    {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen)
    {Z : Scheme.{0}} (r r' : Z ⟶ Y) (hr : r ≫ p = r' ≫ p) (z : Z) (J) (hJ : Good M z J) :
    val u r z J * (val u' r z J)⁻¹ = val u r' z J * (val u' r' z J)⁻¹ := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ := hp (res le (t.s PEmpty.elim)).val
  have key : ∀ r : Z ⟶ Y, (val u r z J * (val u' r z J)⁻¹).val = gs (r ≫ p) z ⊤ a := by
    intro r
    rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
    exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans
      ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a)))
  apply Units.ext
  rw [key, key, hr]

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

theorem surj_fst (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (T : Over S) :
    Function.Surjective (fst T A).left.appTop.hom := by
  have hB : IsAbelianScheme ((Over.pullback T.hom).obj A) :=
    { comm := by have := hA.comm; infer_instance
      smooth := by have := hA.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by have := hA.proper; show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by have := hA.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }
  have hb : Function.Surjective (pullback.snd A.hom T.hom).appTop.hom := (hG _ _ hB).2
  have e : (fst T A).left = (pullbackSymmetry T.hom A.hom).hom ≫ pullback.snd A.hom T.hom :=
    (pullbackSymmetry_hom_comp_snd _ _).symm
  rw [e, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
  have : IsIso (pullbackSymmetry T.hom A.hom).hom.appTop :=
    inferInstanceAs (IsIso ((pullbackSymmetry T.hom A.hom).hom.app ⊤))
  exact (ConcreteCategory.bijective_of_isIso (pullbackSymmetry T.hom A.hom).hom.appTop).2.comp hb

def tval {T : Over S} (θ : ThetaGrp A L k T) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    (J : (Z ⟶ A.left) → L.ι) : (Z.presheaf.stalk z)ˣ :=
  val (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ r z J

theorem commIsOf_iff (hL : L.IsLB) {T : Over S} (θx θy : ThetaGrp A L k T) (c : Γ(T.left, ⊤)ˣ) :
    CommIsOf A L k θx θy c ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      tval θx r z J * tval θy (r ≫ (translT A θx.pt).left) z J =
        tval θy r z J * tval θx (r ≫ (translT A θy.pt).left) z J * gm (r ≫ (fst T A).left) z ⊤ c := by
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J → ∀ θ θ' : ThetaGrp A L k T,
      val (LB.mulGen L _ _ _ _ θ.φ (LB.pullGen L _ _ θ'.φ (translT A θ.pt).left)) r z J =
        tval θ r z J * tval θ' (r ≫ (translT A θ.pt).left) z J := fun Z r z J hJ θ θ' =>
    (val_mul hJ _ _ _).trans (congrArg (tval θ r z J * ·) (val_pull hJ _ _ _))
  constructor
  · intro H Z r z J hJ
    exact (key Z r z J hJ θx θy).symm.trans ((val_corr hJ H r).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (key Z r z J hJ θy θx) (H1.val_constGen L c r z J))))
  · intro H
    refine corr_of_val hL fun y J hJ => ?_
    exact (key _ _ y J hJ θx θy).trans ((H _ _ y J hJ).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (key _ _ y J hJ θy θx) (H1.val_constGen L c _ y J))).symm)

theorem translT_fst {T : Over S} (x : T ⟶ A) : (translT A x).left ≫ (fst T A).left = (fst T A).left := by
  rw [← Over.comp_left, translT, lift_fst]

theorem tval_div (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T : Over S}
    (θ θ' : ThetaGrp A L k T) (h : θ.pt = θ'.pt) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (x : T ⟶ A) (z : Z) (J)
    (hJ : Good L z J) :
    tval θ r z J * (tval θ' r z J)⁻¹ =
      tval θ (r ≫ (translT A x).left) z J * (tval θ' (r ≫ (translT A x).left) z J)⁻¹ := by
  obtain ⟨a, u, hu⟩ := θ
  obtain ⟨a', u', hu'⟩ := θ'
  obtain rfl : a = a' := h
  exact val_div_eq hL (fst T A).left (surj_fst hG hA T) hu hu' r _ (by rw [Category.assoc, translT_fst]) z J hJ

theorem commIsOf_change (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T : Over S}
    {θx θy θx' θy' : ThetaGrp A L k T} {c : Γ(T.left, ⊤)ˣ} (hx : θx'.pt = θx.pt) (hy : θy'.pt = θy.pt)
    (H : CommIsOf A L k θx θy c) : CommIsOf A L k θx' θy' c := by
  rw [commIsOf_iff hL] at H ⊢
  intro Z r z J hJ
  have e₀ := H Z r z J hJ
  have e₁ := tval_div hG hA hL θx' θx hx r θy.pt z J hJ
  have e₂ := tval_div hG hA hL θy' θy hy r θx.pt z J hJ
  rw [hx, hy]
  apply Additive.ofMul.injective
  have a₀ := congrArg Additive.ofMul e₀
  have a₁ := congrArg Additive.ofMul e₁
  have a₂ := congrArg Additive.ofMul e₂
  simp only [ofMul_mul, ofMul_inv] at a₀ a₁ a₂ ⊢
  linear_combination (norm := abel) a₀ + a₁ - a₂

theorem commIsOf_self (hL : L.IsLB) {T : Over S} (θ : ThetaGrp A L k T) : CommIsOf A L k θ θ 1 := by
  rw [commIsOf_iff hL]
  intro Z r z J hJ
  rw [map_one, _root_.mul_one]

theorem commIsOf_symm (hL : L.IsLB) {T : Over S} {θx θy : ThetaGrp A L k T} {c : Γ(T.left, ⊤)ˣ}
    (H : CommIsOf A L k θx θy c) : CommIsOf A L k θy θx c⁻¹ := by
  rw [commIsOf_iff hL] at H ⊢
  intro Z r z J hJ
  rw [H Z r z J hJ, map_inv, mul_inv_cancel_right]

theorem whisker_translPt {T T' : Over S} (h : T' ⟶ T) (x : T ⟶ A) :
    h ▷ A ≫ translPt A x = translPt A (h ≫ x) := by
  show h ▷ A ≫ ((fst T A ≫ x) * snd T A) = (fst T' A ≫ h ≫ x) * snd T' A
  rw [MonObj.comp_mul, whiskerRight_snd, whiskerRight_fst_assoc]

theorem whisker_translT {T T' : Over S} (h : T' ⟶ T) (x : T ⟶ A) :
    translT A (h ≫ x) ≫ h ▷ A = h ▷ A ≫ translT A x := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · simp [translT, whisker_translPt]

theorem exists_pull (hL : L.IsLB) {T T' : Over S} (h : T' ⟶ T) (θ : ThetaGrp A L k T) :
    ∃ θ' : ThetaGrp A L k T', θ'.pt = h ≫ θ.pt ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ A).left) (z : Z) (J),
      Good L z J → tval θ' r z J = tval θ (r ≫ (h ▷ A).left) z J := by
  have e₀ : (h ▷ A).left ≫ (snd T A).left = (snd T' A).left := by rw [← Over.comp_left, whiskerRight_snd]
  have e₁ : (h ▷ A).left ≫ (translPt A θ.pt).left = (translPt A (h ≫ θ.pt)).left := by
    rw [← Over.comp_left, whisker_translPt]
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![(snd T' A).left, (translPt A (h ≫ θ.pt)).left]) (ε' := ![k, -k])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ k) e₀
      · exact congrArg (fun q => f q ^ (-k)) e₁)
    (LB.pullGen L ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] θ.φ (h ▷ A).left)
    (DVR.pullGen_isGen _ _ _ _ θ.isGen _)
  exact ⟨⟨h ≫ θ.pt, t, ht⟩, rfl, fun Z r z J hJ => (hv Z r z J hJ).trans (val_pull hJ _ _ _)⟩

theorem exists_commIsOf_pull (hL : L.IsLB) {T T' : Over S} (h : T' ⟶ T) {θx θy : ThetaGrp A L k T}
    {c : Γ(T.left, ⊤)ˣ} (H : CommIsOf A L k θx θy c) :
    ∃ θx' θy' : ThetaGrp A L k T', θx'.pt = h ≫ θx.pt ∧ θy'.pt = h ≫ θy.pt ∧
      CommIsOf A L k θx' θy' (Units.map h.left.appTop.hom.toMonoidHom c) := by
  obtain ⟨θx', hx, vx⟩ := exists_pull hL h θx
  obtain ⟨θy', hy, vy⟩ := exists_pull hL h θy
  refine ⟨θx', θy', hx, hy, ?_⟩
  rw [commIsOf_iff hL] at H ⊢
  intro Z r z J hJ
  have t : ∀ x : T ⟶ A, (r ≫ (translT A (h ≫ x)).left) ≫ (h ▷ A).left =
      (r ≫ (h ▷ A).left) ≫ (translT A x).left := fun x => by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whisker_translT]
  have g : gm (r ≫ (fst T' A).left) z ⊤ (Units.map h.left.appTop.hom.toMonoidHom c) =
      gm ((r ≫ (h ▷ A).left) ≫ (fst T A).left) z ⊤ c := by
    refine (gm_pull (r ≫ (fst T' A).left) h.left z ⊤ trivial c).trans ?_
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whiskerRight_fst]
  rw [vx _ _ z J hJ, vx _ _ z J hJ, vy _ _ z J hJ, vy _ _ z J hJ, hx, hy, t, t, g]
  exact H Z _ z J hJ

theorem weilIs_symm (hL : L.IsLB) {T : Over S} {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (H : WeilIs A L k x y c) :
    WeilIs A L k y x c⁻¹ := by
  intro p
  obtain ⟨V, hp, ⟨θx, θy, hx, hy⟩, hc⟩ := H p
  refine ⟨V, hp, ⟨θy, θx, hy, hx⟩, fun θy θx hy hx => ?_⟩
  have e : unitRes V c⁻¹ = (unitRes V c)⁻¹ := map_inv _ _
  rw [e]
  exact commIsOf_symm hL (hc θx θy hx hy)

theorem weilIs_pull (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T T' : Over S} (h : T' ⟶ T)
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (H : WeilIs A L k x y c) :
    WeilIs A L k (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom c) := by
  intro p
  obtain ⟨V, hp, ⟨θx, θy, hx, hy⟩, hc⟩ := H (h.left p)
  have w : (h.left ∣_ V) ≫ V.ι = (h.left ⁻¹ᵁ V).ι ≫ h.left := morphismRestrict_ι _ _
  let h' : overRes (h.left ⁻¹ᵁ V) ⟶ overRes V := Over.homMk (h.left ∣_ V) (by
    show (h.left ∣_ V) ≫ V.ι ≫ T.hom = (h.left ⁻¹ᵁ V).ι ≫ T'.hom
    rw [← Category.assoc, w, Category.assoc, Over.w h])
  have w' : h' ≫ overResι V = overResι (h.left ⁻¹ᵁ V) ≫ h := Over.OverMorphism.ext w
  obtain ⟨θx', θy', hx', hy', H'⟩ := exists_commIsOf_pull hL h' (hc θx θy hx hy)
  rw [hx, ← Category.assoc, w', Category.assoc] at hx'
  rw [hy, ← Category.assoc, w', Category.assoc] at hy'
  have e : Units.map h'.left.appTop.hom.toMonoidHom (unitRes V c) =
      unitRes (h.left ⁻¹ᵁ V) (Units.map h.left.appTop.hom.toMonoidHom c) := by
    apply Units.ext
    have := congrArg (fun q => q.appTop.hom c.val) w
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at this
    exact this
  rw [e] at H'
  exact ⟨h.left ⁻¹ᵁ V, hp, ⟨θx', θy', hx', hy'⟩, fun a b ha hb =>
    commIsOf_change hG hA hL (ha.trans hx'.symm) (hb.trans hy'.symm) H'⟩

end GlobalTheory.CommPairing

namespace GlobalTheory

open CommPairing in

theorem weilIs_alternating_skew_natural : GlobalFnsSt → (∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A), x ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp P.A P.L N (overRes V), θ.pt = overResι V ≫ x) → ∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S), (∀ x : T ⟶ P.A, x ^ k = 1 → WeilIs P.A P.L k x x 1) ∧ (∀ (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k y x c⁻¹) ∧ ∀ (T' : Over S) (h : T' ⟶ T) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom c) := by
  intro hG hlift S P k T
  refine ⟨fun x hx p => ?_, fun x y c H => weilIs_symm P.isLB H,
    fun T' h x y c H => weilIs_pull hG P.isAb P.isLB h H⟩
  obtain ⟨V, hp, θ, hθ⟩ := hlift S P k T x hx p
  refine ⟨V, hp, ⟨θ, θ, hθ, hθ⟩, fun a b ha hb => ?_⟩
  have e : unitRes V (1 : Γ(T.left, ⊤)ˣ) = 1 := map_one _
  rw [e]
  exact commIsOf_change hG P.isAb P.isLB (ha.trans hθ.symm) (hb.trans hθ.symm) (commIsOf_self P.isLB θ)

end GlobalTheory
