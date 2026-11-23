import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CommutatorPairing

theorem exists_ratio {X Y S₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ c : Γ(S₀, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      val u r z J = val u' r z J * gm (r ≫ p) z ⊤ c := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, hF U h, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ := hp (res le (t.s PEmpty.elim)).val
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      val u r z J * (val u' r z J)⁻¹ = gm r z ⊤ (res le (t.s PEmpty.elim)) := by
    intro Z r z J hJ
    rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
    exact (gm_res r z le trivial _).symm
  have key' : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z),
      (gm r z ⊤ (res le (t.s PEmpty.elim))).val = gs (r ≫ p) z ⊤ a := fun Z r z =>
    (gs_unit r z ⊤ trivial _).symm.trans ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a))
  refine ⟨pullU e ⊤ (res le (t.s PEmpty.elim)), fun Z r z J hJ => ?_⟩
  have h₁ := gm_pull (r ≫ p) e z ⊤ trivial (res le (t.s PEmpty.elim))
  have h₂ : gm ((r ≫ p) ≫ e) z ⊤ (res le (t.s PEmpty.elim)) = gm r z ⊤ (res le (t.s PEmpty.elim)) :=
    Units.ext (by rw [key', key', Category.assoc, he, Category.comp_id])
  have h₃ := (h₁.trans h₂).trans (key Z r z J hJ).symm
  exact Eq.trans (by rw [mul_comm, inv_mul_cancel_right]) (congrArg (val u' r z J * ·) h₃.symm)

theorem glue_top {Y : Scheme.{0}} {ι' : Type} (W : ι' → Y.Opens) (hW : ∀ y, ∃ s, y ∈ W s)
    (c : ∀ s, Γ((W s).toScheme, ⊤)ˣ)
    (agree : ∀ s s' (Z : Scheme.{0}) (r : Z ⟶ (W s).toScheme) (r' : Z ⟶ (W s').toScheme) (z : Z),
      r ≫ (W s).ι = r' ≫ (W s').ι → gm r z ⊤ (c s) = gm r' z ⊤ (c s')) :
    ∃ a : Γ(Y, ⊤)ˣ, ∀ s (Z : Scheme.{0}) (r : Z ⟶ (W s).toScheme) (z : Z),
      gm (r ≫ (W s).ι) z ⊤ a = gm r z ⊤ (c s) := by
  choose b hb using fun s => exists_ext_unit (W s).ι ⊤ (c s)
  obtain ⟨a, ha⟩ := glue_unit (⊤ : Y.Opens) _ (fun s => le_top) (fun y _ => by
      obtain ⟨s, hs⟩ := hW y
      exact Opens.mem_iSup.2 ⟨s, ⟨y, hs⟩, trivial, rfl⟩) b (fun s s' y hy => by
      obtain ⟨⟨y₁, h₁, e₁⟩, ⟨y₂, h₂, e₂⟩⟩ := hy
      have hy₁ : y ∈ W s := e₁ ▸ y₁.2
      have hy₂ : y ∈ W s' := e₂ ▸ y₂.2
      let z : (W s ⊓ W s').toScheme := ⟨y, hy₁, hy₂⟩
      let r := Y.homOfLE (inf_le_left : W s ⊓ W s' ≤ W s)
      let r' := Y.homOfLE (inf_le_right : W s ⊓ W s' ≤ W s')
      have f₁ : r ≫ (W s).ι = (W s ⊓ W s').ι := Y.homOfLE_ι _
      have f₂ : r' ≫ (W s').ι = (W s ⊓ W s').ι := Y.homOfLE_ι _
      have b₁ := hb s _ r z trivial
      have b₂ := hb s' _ r' z trivial
      rw [f₁] at b₁
      rw [f₂] at b₂
      have n₁ : (W s ⊓ W s').ι z ∈ (W s).ι ''ᵁ ⊤ := ⟨y₁, h₁, e₁⟩
      have n₂ : (W s ⊓ W s').ι z ∈ (W s').ι ''ᵁ ⊤ := ⟨y₂, h₂, e₂⟩
      exact gm_inj (W s ⊓ W s').ι z n₁ n₂ (b₁.trans ((agree s s' _ r r' z (f₁.trans f₂.symm)).trans b₂.symm)))
  refine ⟨a, fun s Z r z => ?_⟩
  have hm : (r ≫ (W s).ι) z ∈ (W s).ι ''ᵁ ⊤ := ⟨r z, trivial, rfl⟩
  exact (gm_res _ z le_top hm a).symm.trans ((congrArg (gm _ z _) (ha s)).trans (hb s Z r z trivial))

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem surj_fst (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (T : Over S) :
    Function.Surjective (fst T A).left.appTop.hom := by
  have e : (fst T A).left = (β_ T A).hom.left ≫ (snd A T).left := by
    rw [← Over.comp_left, braiding_hom_snd]
  rw [e]
  refine surj_comp ?_ (surj_snd hG hA T)
  have : IsIso (β_ T A).hom.left := inferInstanceAs (IsIso ((Over.forget S).map (β_ T A).hom))
  have : IsIso (β_ T A).hom.left.appTop := inferInstanceAs (IsIso ((β_ T A).hom.left.app ⊤))
  exact (ConcreteCategory.bijective_of_isIso (β_ T A).hom.left.appTop).2

theorem lift_translPt {T Z : Over S} (x : T ⟶ A) (t : Z ⟶ T) (a : Z ⟶ A) :
    lift t a ≫ translPt A x = (t ≫ x) * a := by
  simp [translPt, Hom.mul_def, comp_lift_assoc]

theorem lift_translT {T Z : Over S} (x : T ⟶ A) (t : Z ⟶ T) (a : Z ⟶ A) :
    lift t a ≫ translT A x = lift t ((t ≫ x) * a) := by
  rw [translT, comp_lift, lift_fst, lift_translPt]

variable {L : LB A.left} {k : ℤ}

def thetaVal {T Z : Over S} (θ : ThetaGrp A L k T) (t : Z ⟶ T) (a : Z ⟶ A) (z : Z.left)
    (J : (Z.left ⟶ A.left) → L.ι) : (Z.left.presheaf.stalk z)ˣ :=
  val (L := L) (K := Fin 2) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (lift t a).left z J

def commVal {T Z : Over S} (θx θy : ThetaGrp A L k T) (t : Z ⟶ T) (a : Z ⟶ A) (z : Z.left)
    (J : (Z.left ⟶ A.left) → L.ι) : (Z.left.presheaf.stalk z)ˣ :=
  thetaVal θx t a z J * thetaVal θy t ((t ≫ θx.pt) * a) z J *
    (thetaVal θy t a z J * thetaVal θx t ((t ≫ θy.pt) * a) z J)⁻¹

theorem prod_theta {T Z : Over S} (x : T ⟶ A) (t : Z ⟶ T) (a : Z ⟶ A) {U : Type} [CommGroup U]
    (h : (Z.left ⟶ A.left) → U) :
    ∏ i : Fin 2, h ((lift t a).left ≫ ![(snd T A).left, (translPt A x).left] i) ^ ![k, -k] i =
      h a.left ^ k * h ((t ≫ x) * a).left ^ (-k) := by
  rw [Fin.prod_univ_two]
  show h (lift t a ≫ snd T A).left ^ k * h (lift t a ≫ translPt A x).left ^ (-k) = _
  rw [lift_snd, lift_translPt]

theorem val_transl {T Z : Over S} (θ : ThetaGrp A L k T) (x : T ⟶ A) (t : Z ⟶ T) (a : Z ⟶ A) {z : Z.left} {J}
    (hJ : Good L z J) :
    val (LB.pullGen L (K := Fin 2) ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] θ.φ (translT A x).left)
      (lift t a).left z J = thetaVal θ t ((t ≫ x) * a) z J := by
  refine (val_pull hJ _ _ _).trans ?_
  rw [← Over.comp_left, lift_translT]; rfl

theorem val_prod {T Z : Over S} (θ θ' : ThetaGrp A L k T) (t : Z ⟶ T) (a : Z ⟶ A) {z : Z.left} {J}
    (hJ : Good L z J) :
    val (LB.mulGen L _ _ _ _ θ.φ (LB.pullGen L _ _ θ'.φ (translT A θ.pt).left)) (lift t a).left z J =
      thetaVal θ t a z J * thetaVal θ' t ((t ≫ θ.pt) * a) z J :=
  (val_mul hJ _ _ _).trans (congrArg (thetaVal θ t a z J * ·) (val_transl θ' _ t a hJ))

omit [GrpObj A] in
theorem val_const {T Z : Over S} (c : Γ(T.left, ⊤)ˣ) (t : Z ⟶ T) (a : Z ⟶ A) (z : Z.left) (J) :
    val (constGen A L c) (lift t a).left z J = gm t.left z ⊤ c := by
  have e : t.left = (lift t a).left ≫ (fst T A).left := by rw [← Over.comp_left, lift_fst]
  rw [e]
  exact (gm_res _ z le_top (Set.mem_iInter.2 fun k => k.elim) _).trans (gm_pull _ (fst T A).left z ⊤ trivial c)

theorem commIsOf_iff (hL : L.IsLB) {T : Over S} (θx θy : ThetaGrp A L k T) (c : Γ(T.left, ⊤)ˣ) :
    CommIsOf A L k θx θy c ↔ ∀ (Z : Over S) (t : Z ⟶ T) (a : Z ⟶ A) (z : Z.left) (J), Good L z J →
      commVal θx θy t a z J = gm t.left z ⊤ c := by
  constructor
  · intro h Z t a z J hJ
    have := val_corr hJ h (lift t a).left
    exact mul_inv_eq_iff_eq_mul.2 ((val_prod θx θy t a hJ).symm.trans (this.trans ((val_mul hJ _ _ _).trans
      ((congrArg₂ (· * ·) (val_prod θy θx t a hJ) (val_const c t a z J)).trans (mul_comm _ _)))))
  · intro h
    refine corr_of_val hL fun y J hJ => ?_
    have e : 𝟙 (T ⊗ A).left = (lift (fst T A) (snd T A)).left := by rw [lift_fst_snd]; rfl
    rw [e]
    exact (val_prod θx θy _ _ hJ).trans (((mul_inv_eq_iff_eq_mul.1 (h _ (fst T A) (snd T A) y J hJ)).trans
      (mul_comm _ _)).trans ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (val_prod θy θx _ _ hJ) (val_const c _ _ y J))).symm)

theorem exists_pull (hL : L.IsLB) {T T' : Over S} (θ : ThetaGrp A L k T) (t : T' ⟶ T) :
    ∃ θ' : ThetaGrp A L k T', θ'.pt = t ≫ θ.pt := by
  obtain ⟨u, hu, -⟩ := exists_gen hL (K' := Fin 2) (φ' := ![(snd T' A).left, (translPt A (t ≫ θ.pt)).left])
    (ε' := ![k, -k]) (fun U _ h => by
      refine (prod_theta θ.pt (fst T' A ≫ t) (snd T' A) h).trans ?_
      rw [Fin.prod_univ_two, Category.assoc]; rfl)
    (LB.pullGen L (K := Fin 2) ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] θ.φ
      (lift (fst T' A ≫ t) (snd T' A)).left) (DVR.pullGen_isGen _ _ _ _ θ.isGen _)
  exact ⟨⟨t ≫ θ.pt, u, hu⟩, rfl⟩

theorem thetaVal_ratio (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T T' Z : Over S}
    (θ : ThetaGrp A L k T) (θ' : ThetaGrp A L k T') (t : Z ⟶ T) (t' : Z ⟶ T') (h : t ≫ θ.pt = t' ≫ θ'.pt)
    (z : Z.left) : ∃ u : (Z.left.presheaf.stalk z)ˣ, ∀ (a : Z ⟶ A) (J), Good L z J →
      thetaVal θ t a z J = thetaVal θ' t' a z J * u := by
  obtain ⟨c, hc⟩ := exists_ratio hL (fun U _ g => by
      refine (prod_theta θ.pt (fst Z A ≫ t) (snd Z A) g).trans
        (Eq.trans ?_ (prod_theta θ'.pt (fst Z A ≫ t') (snd Z A) g).symm)
      rw [Category.assoc, Category.assoc, h]) (fst Z A).left (lift (𝟙 Z) 1).left
      (by rw [← Over.comp_left, lift_fst]; rfl) (surj_fst hG hA Z)
    (DVR.pullGen_isGen _ _ _ _ θ.isGen (lift (fst Z A ≫ t) (snd Z A)).left)
    (DVR.pullGen_isGen _ _ _ _ θ'.isGen (lift (fst Z A ≫ t') (snd Z A)).left)
  refine ⟨gm (𝟙 _) z ⊤ c, fun a J hJ => ?_⟩
  have := (val_pull hJ _ _ _).symm.trans ((hc _ (lift (𝟙 Z) a).left z J hJ).trans
    (congrArg (· * _) (val_pull hJ _ _ _)))
  rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift,
    lift_fst_assoc, lift_fst_assoc, lift_snd, lift_fst, Category.id_comp, Category.id_comp] at this
  exact this

theorem commVal_indep (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T T' Z : Over S}
    (θx θy : ThetaGrp A L k T) (θx' θy' : ThetaGrp A L k T') (t : Z ⟶ T) (t' : Z ⟶ T')
    (hx : t ≫ θx.pt = t' ≫ θx'.pt) (hy : t ≫ θy.pt = t' ≫ θy'.pt) (a : Z ⟶ A) (z : Z.left) (J) (hJ : Good L z J) :
    commVal θx θy t a z J = commVal θx' θy' t' a z J := by
  obtain ⟨u, hu⟩ := thetaVal_ratio hG hA hL θx θx' t t' hx z
  obtain ⟨v, hv⟩ := thetaVal_ratio hG hA hL θy θy' t t' hy z
  rw [commVal, commVal, hu _ J hJ, hu _ J hJ, hv _ J hJ, hv _ J hJ, hx, hy]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_commIsOf (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T : Over S}
    (θx θy : ThetaGrp A L k T) : ∃ c : Γ(T.left, ⊤)ˣ, CommIsOf A L k θx θy c := by
  have := hA.comm
  have p₁ : ∀ (x : T ⟶ A) (U : Type) [CommGroup U] (g : ((T ⊗ A).left ⟶ A.left) → U),
      ∏ i : Fin 2, g (![(snd T A).left, (translPt A x).left] i) ^ ![k, -k] i =
        g (snd T A).left ^ k * g ((fst T A ≫ x) * snd T A).left ^ (-k) := fun x U _ g => by
    rw [Fin.prod_univ_two]; rfl
  obtain ⟨c, hc⟩ := exists_ratio hL (fun U _ g => by
      refine (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _ (p₁ θx.pt U g)
        (prod_theta θy.pt (fst T A) ((fst T A ≫ θx.pt) * snd T A) g)).trans (Eq.trans ?_
        (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _ (p₁ θy.pt U g)
          (prod_theta θx.pt (fst T A) ((fst T A ≫ θy.pt) * snd T A) g)).symm)
      rw [mul_left_comm (fst T A ≫ θy.pt)]
      simp only [zpow_neg, _root_.mul_assoc, inv_mul_cancel_left]) (fst T A).left (lift (𝟙 T) 1).left
      (by rw [← Over.comp_left, lift_fst]; rfl) (surj_fst hG hA T)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ θx.isGen (DVR.pullGen_isGen _ _ _ _ θy.isGen (translT A θx.pt).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ θy.isGen (DVR.pullGen_isGen _ _ _ _ θx.isGen (translT A θy.pt).left))
  refine ⟨c, (commIsOf_iff hL θx θy c).2 fun Z t a z J hJ => ?_⟩
  have := (val_prod θx θy t a hJ).symm.trans ((hc _ (lift t a).left z J hJ).trans
    (congrArg (· * _) (val_prod θy θx t a hJ)))
  rw [← Over.comp_left, lift_fst] at this
  exact mul_inv_eq_iff_eq_mul.2 (this.trans (mul_comm _ _))

theorem gm_unitRes {T : Over S} (V : T.left.Opens) (c : Γ(T.left, ⊤)ˣ) {Z : Scheme.{0}} (r : Z ⟶ V.toScheme) (z : Z) :
    gm r z ⊤ (unitRes V c) = gm (r ≫ V.ι) z ⊤ c := gm_pull r V.ι z ⊤ trivial c

def overLE {T : Over S} {V W : T.left.Opens} (h : V ≤ W) : overRes V ⟶ overRes W :=
  Over.homMk (T.left.homOfLE h) (by
    show T.left.homOfLE h ≫ W.ι ≫ T.hom = V.ι ≫ T.hom
    rw [← Category.assoc, Scheme.homOfLE_ι])

theorem overLE_ι {T : Over S} {V W : T.left.Opens} (h : V ≤ W) : overLE h ≫ overResι W = overResι V :=
  Over.OverMorphism.ext (T.left.homOfLE_ι h)

theorem weilIs_unique (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T : Over S} {x y : T ⟶ A}
    {c c' : Γ(T.left, ⊤)ˣ} (h : WeilIs A L k x y c) (h' : WeilIs A L k x y c') : c = c' := by
  refine unit_ext fun p _ => ?_
  obtain ⟨V, hV, ⟨θx, θy, hx, hy⟩, H⟩ := h p
  obtain ⟨V', hV', ⟨θx', θy', hx', hy'⟩, H'⟩ := h' p
  let z : (V ⊓ V').toScheme := ⟨p, hV, hV'⟩
  let t := overLE (inf_le_left : V ⊓ V' ≤ V)
  let t' := overLE (inf_le_right : V ⊓ V' ≤ V')
  choose J hJ using fun χ : (overRes (V ⊓ V')).left ⟶ A.left => exists_chart hL (χ z)
  have e₁ := (commIsOf_iff hL _ _ _).1 (H θx θy hx hy) _ t 1 z J hJ
  have e₂ := (commIsOf_iff hL _ _ _).1 (H' θx' θy' hx' hy') _ t' 1 z J hJ
  have e₃ := commVal_indep hG hA hL θx θy θx' θy' t t'
    (by rw [hx, hx', ← Category.assoc, ← Category.assoc, overLE_ι, overLE_ι])
    (by rw [hy, hy', ← Category.assoc, ← Category.assoc, overLE_ι, overLE_ι]) 1 z J hJ
  have f₁ := gm_unitRes V c (T.left.homOfLE (inf_le_left : V ⊓ V' ≤ V)) z
  have f₂ := gm_unitRes V' c' (T.left.homOfLE (inf_le_right : V ⊓ V' ≤ V')) z
  rw [Scheme.homOfLE_ι] at f₁ f₂
  exact gm_inj (V ⊓ V').ι z (U := ⊤) (U' := ⊤) trivial trivial (f₁.symm.trans (e₁.symm.trans (e₃.trans (e₂.trans f₂))))

theorem exists_weilIs (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T : Over S} {x y : T ⟶ A}
    (hx : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp A L k (overRes V), θ.pt = overResι V ≫ x)
    (hy : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp A L k (overRes V), θ.pt = overResι V ≫ y) :
    ∃ c : Γ(T.left, ⊤)ˣ, WeilIs A L k x y c := by
  have loc : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θx θy : ThetaGrp A L k (overRes V),
      θx.pt = overResι V ≫ x ∧ θy.pt = overResι V ≫ y := fun p => by
    obtain ⟨V, hV, θ, e⟩ := hx p
    obtain ⟨V', hV', θ', e'⟩ := hy p
    obtain ⟨θx, ex⟩ := exists_pull hL θ (overLE (inf_le_left : V ⊓ V' ≤ V))
    obtain ⟨θy, ey⟩ := exists_pull hL θ' (overLE (inf_le_right : V ⊓ V' ≤ V'))
    exact ⟨V ⊓ V', ⟨hV, hV'⟩, θx, θy, by rw [ex, e, ← Category.assoc, overLE_ι],
      by rw [ey, e', ← Category.assoc, overLE_ι]⟩
  choose V hV θx θy ex ey using loc
  choose c hc using fun p => exists_commIsOf hG hA hL (θx p) (θy p)
  obtain ⟨a, ha⟩ := glue_top V (fun p => ⟨p, hV p⟩) c (fun s s' Z r r' z hr => by
    let Z' : Over S := Over.mk (r ≫ (V s).ι ≫ T.hom)
    let t : Z' ⟶ overRes (V s) := Over.homMk r rfl
    let t' : Z' ⟶ overRes (V s') := Over.homMk r' (by
      show r' ≫ (V s').ι ≫ T.hom = r ≫ (V s).ι ≫ T.hom
      rw [← Category.assoc, ← hr, Category.assoc])
    have ht : t ≫ overResι (V s) = t' ≫ overResι (V s') := Over.OverMorphism.ext hr
    choose J hJ using fun χ : Z ⟶ A.left => exists_chart hL (χ z)
    have e₁ := (commIsOf_iff hL _ _ _).1 (hc s) _ t 1 z J hJ
    have e₂ := (commIsOf_iff hL _ _ _).1 (hc s') _ t' 1 z J hJ
    have e₃ := commVal_indep hG hA hL (θx s) (θy s) (θx s') (θy s') t t'
      (by rw [ex, ex, ← Category.assoc, ← Category.assoc, ht])
      (by rw [ey, ey, ← Category.assoc, ← Category.assoc, ht]) 1 z J hJ
    exact e₁.symm.trans (e₃.trans e₂))
  refine ⟨a, fun p => ⟨V p, hV p, ⟨θx p, θy p, ex p, ey p⟩, fun θ θ' e e' => ?_⟩⟩
  refine (commIsOf_iff hL _ _ _).2 fun Z t b z J hJ => ?_
  exact (commVal_indep hG hA hL θ θ' (θx p) (θy p) t t (by rw [e, ex]) (by rw [e', ey]) b z J hJ).trans
    (((commIsOf_iff hL _ _ _).1 (hc p) _ t b z J hJ).trans ((ha p _ t.left z).symm.trans
      (gm_unitRes (V p) a t.left z).symm))

theorem existsUnique_weilIs : GlobalFnsSt → (∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A),
    x ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : ThetaGrp P.A P.L N (overRes V), θ.pt = overResι V ≫ x) →
    ∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S) (x y : T ⟶ P.A), x ^ k = 1 → y ^ k = 1 →
      ∃! c : Γ(T.left, ⊤)ˣ, WeilIs P.A P.L k x y c := by
  intro hG hl S P k T x y hx hy
  obtain ⟨c, hc⟩ := exists_weilIs hG P.isAb P.isLB (hl S P k T x hx) (hl S P k T y hy)
  exact ⟨c, hc, fun c' hc' => weilIs_unique hG P.isAb P.isLB hc' hc⟩

end GlobalTheory.CommutatorPairing
