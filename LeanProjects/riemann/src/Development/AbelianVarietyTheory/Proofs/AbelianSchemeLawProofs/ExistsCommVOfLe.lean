import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilMul

theorem exists_ratio {X Y S₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (p : Y ⟶ S₀) (hp : Function.Surjective p.appTop.hom)
    {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ a : Γ(S₀, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J * (val u' r z J)⁻¹).val = gs (r ≫ p) z ⊤ a := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ := hp (res le (t.s PEmpty.elim)).val
  refine ⟨a, fun Z r z J hJ => ?_⟩
  rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans
    ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a)))

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

def tv {T T' : Over S} (θ : ThetaGrp A L k T) (t : T' ⟶ T) (a : T' ⟶ A) (z : T'.left)
    (J : (T'.left ⟶ A.left) → L.ι) : (T'.left.presheaf.stalk z)ˣ :=
  val (L := L) (K := Fin 2) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (lift t a).left z J

theorem lift_translPt {T T' : Over S} (x : T ⟶ A) (t : T' ⟶ T) (a : T' ⟶ A) :
    lift t a ≫ translPt A x = (t ≫ x) * a := by
  rw [translPt, ← Category.assoc, comp_lift, lift_snd, lift_fst_assoc, Hom.mul_def]

theorem lift_translT {T T' : Over S} (x : T ⟶ A) (t : T' ⟶ T) (a : T' ⟶ A) :
    lift t a ≫ translT A x = lift t ((t ≫ x) * a) := by
  rw [translT, comp_lift, lift_fst, lift_translPt]

theorem prod_theta {T T' : Over S} (x : T ⟶ A) (t : T' ⟶ T) (a : T' ⟶ A) {U : Type} [CommGroup U]
    (h : (T'.left ⟶ A.left) → U) :
    ∏ i : Fin 2, h ((lift t a).left ≫ ![(snd T A).left, (translPt A x).left] i) ^ (![k, -k] i) =
      h a.left ^ k * h ((t ≫ x) * a).left ^ (-k) := by
  rw [Fin.prod_univ_two]
  show h (lift t a ≫ snd T A).left ^ k * h (lift t a ≫ translPt A x).left ^ (-k) = _
  rw [lift_snd, lift_translPt]

theorem prod_theta_id {T : Over S} (x : T ⟶ A) {U : Type} [CommGroup U]
    (h : ((T ⊗ A).left ⟶ A.left) → U) :
    ∏ i : Fin 2, h (![(snd T A).left, (translPt A x).left] i) ^ (![k, -k] i) =
      h (snd T A).left ^ k * h ((fst T A ≫ x) * snd T A).left ^ (-k) := by
  rw [Fin.prod_univ_two]
  rfl

theorem val_pull_tv {T T₁ T' : Over S} (θ : ThetaGrp A L k T) (t : T₁ ⟶ T) (a : T₁ ⟶ A) (ρ : T' ⟶ T₁)
    {z : T'.left} {J} (hJ : Good L z J) :
    val (LB.pullGen L (K := Fin 2) ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] θ.φ (lift t a).left)
      ρ.left z J = tv θ (ρ ≫ t) (ρ ≫ a) z J := by
  refine (val_pull hJ _ _ _).trans ?_
  rw [← Over.comp_left, comp_lift]; rfl

def CommV {T T₀ : Over S} (θx θy : ThetaGrp A L k T) (g : T ⟶ T₀) (c : Γ(T₀.left, ⊤)ˣ) : Prop :=
  ∀ (T' : Over S) (t : T' ⟶ T) (a : T' ⟶ A) (z : T'.left) (J), Good L z J →
    tv θx t a z J * tv θy t ((t ≫ θx.pt) * a) z J =
      tv θy t a z J * tv θx t ((t ≫ θy.pt) * a) z J * gm (t ≫ g).left z ⊤ c

theorem val_const {T T' : Over S} (V : T.left.Opens) (c : Γ(T.left, ⊤)ˣ) (t : T' ⟶ overRes V) (a : T' ⟶ A)
    (z : T'.left) (J) :
    val (constGen A L (unitRes V c)) (lift t a).left z J = gm (t ≫ overResι V).left z ⊤ c := by
  have hm : (lift t a).left z ∈ LB.wchart L (PEmpty.elim : PEmpty → ((overRes V ⊗ A).left ⟶ A.left)) PEmpty.elim :=
    Set.mem_iInter.2 fun k => k.elim
  rw [val_of _ _ z J PEmpty.elim (fun k => k.elim)]
  refine (gm_res _ z le_top hm _).trans ((gm_pull (lift t a).left (fst (overRes V) A).left z ⊤ trivial _).trans ?_)
  rw [← Over.comp_left, lift_fst]
  exact gm_pull t.left V.ι z ⊤ trivial c

theorem commIs_iff (hL : L.IsLB) {T : Over S} (V : T.left.Opens) (θx θy : ThetaGrp A L k (overRes V))
    (c : Γ(T.left, ⊤)ˣ) : CommIsOf A L k θx θy (unitRes V c) ↔ CommV θx θy (overResι V) c := by
  have e : ∀ (θ θ' : ThetaGrp A L k (overRes V)) (T' : Over S) (t : T' ⟶ overRes V) (a : T' ⟶ A) (z : T'.left) (J),
      Good L z J → val (LB.mulGen L _ _ _ _ θ.φ (LB.pullGen L _ _ θ'.φ (translT A θ.pt).left)) (lift t a).left z J =
        tv θ t a z J * tv θ' t ((t ≫ θ.pt) * a) z J := fun θ θ' T' t a z J hJ => by
    refine (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans ?_))
    rw [← Over.comp_left, lift_translT]; rfl
  constructor
  · intro h T' t a z J hJ
    exact (e θx θy _ t a z J hJ).symm.trans ((val_corr hJ h (lift t a).left).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (e θy θx _ t a z J hJ) (val_const V c t a z J))))
  · intro h
    refine corr_of_val hL fun y J hJ => ?_
    have i : 𝟙 (overRes V ⊗ A).left = (lift (fst (overRes V) A) (snd (overRes V) A)).left := by
      rw [lift_fst_snd]; rfl
    rw [i]
    exact (e θx θy _ _ _ y J hJ).trans ((h _ _ _ y J hJ).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (e θy θx _ _ _ y J hJ) (val_const V c _ _ y J))).symm)

theorem exists_restrict (hL : L.IsLB) {T T₁ : Over S} (θ : ThetaGrp A L k T) (f : T₁ ⟶ T) :
    ∃ θ₁ : ThetaGrp A L k T₁, θ₁.pt = f ≫ θ.pt ∧ ∀ (T' : Over S) (t : T' ⟶ T₁) (a : T' ⟶ A) (z : T'.left) (J),
      Good L z J → tv θ₁ t a z J = tv θ (t ≫ f) a z J := by
  obtain ⟨u, hu, hv⟩ := exists_gen hL (K' := Fin 2) (φ' := ![(snd T₁ A).left, (translPt A (f ≫ θ.pt)).left])
    (ε' := ![k, -k]) (fun U _ h => by
      refine (prod_theta θ.pt (fst T₁ A ≫ f) (snd T₁ A) h).trans ?_
      rw [prod_theta_id, Category.assoc])
    (LB.pullGen L (K := Fin 2) ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] θ.φ
      (lift (fst T₁ A ≫ f) (snd T₁ A)).left) (DVR.pullGen_isGen _ _ _ _ θ.isGen _)
  refine ⟨⟨f ≫ θ.pt, u, hu⟩, rfl, fun T' t a z J hJ => ?_⟩
  refine (hv _ _ z J hJ).trans ((val_pull_tv θ _ _ (lift t a) hJ).trans ?_)
  rw [lift_fst_assoc, lift_snd]

theorem exists_mul [IsCommMonObj A] (hL : L.IsLB) {T : Over S} (θ θ' : ThetaGrp A L k T) :
    ∃ θ₁ : ThetaGrp A L k T, θ₁.pt = θ.pt * θ'.pt ∧ ∀ (T' : Over S) (t : T' ⟶ T) (a : T' ⟶ A) (z : T'.left) (J),
      Good L z J → tv θ₁ t a z J = tv θ t a z J * tv θ' t ((t ≫ θ.pt) * a) z J := by
  obtain ⟨u, hu, hv⟩ := exists_gen hL (K' := Fin 2) (φ' := ![(snd T A).left, (translPt A (θ.pt * θ'.pt)).left])
    (ε' := ![k, -k]) (fun U _ h => by
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (prod_theta_id θ.pt h)
        (prod_theta θ'.pt (fst T A) ((fst T A ≫ θ.pt) * snd T A) h))).trans ?_
      rw [prod_theta_id, MonObj.comp_mul, mul_comm (fst T A ≫ θ.pt) (fst T A ≫ θ'.pt),
        _root_.mul_assoc (fst T A ≫ θ'.pt)]
      simp only [zpow_neg, _root_.mul_assoc, inv_mul_cancel_left])
    (LB.mulGen L _ _ _ _ θ.φ (LB.pullGen L (K := Fin 2) ![(snd T A).left, (translPt A θ'.pt).left] ![k, -k] θ'.φ
      (lift (fst T A) ((fst T A ≫ θ.pt) * snd T A)).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ θ.isGen (DVR.pullGen_isGen _ _ _ _ θ'.isGen _))
  refine ⟨⟨θ.pt * θ'.pt, u, hu⟩, rfl, fun T' t a z J hJ => ?_⟩
  refine (hv _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl
    ((val_pull_tv θ' _ _ (lift t a) hJ).trans ?_)))
  rw [MonObj.comp_mul, lift_fst_assoc, lift_snd, lift_fst]

theorem ratio_const (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T : Over S}
    (θ θ' : ThetaGrp A L k T) (h : θ.pt = θ'.pt) {T' : Over S} (t : T' ⟶ T) (a b : T' ⟶ A) {z : T'.left} {J}
    (hJ : Good L z J) : tv θ t a z J * (tv θ' t a z J)⁻¹ = tv θ t b z J * (tv θ' t b z J)⁻¹ := by
  obtain ⟨x, φ, hφ⟩ := θ
  obtain ⟨x', φ', hφ'⟩ := θ'
  obtain rfl : x = x' := h
  obtain ⟨c, hc⟩ := exists_ratio hL (snd A T).left (surj_snd hG hA T)
    (DVR.pullGen_isGen _ _ _ _ hφ (lift (snd A T) (fst A T)).left)
    (DVR.pullGen_isGen _ _ _ _ hφ' (lift (snd A T) (fst A T)).left)
  have key : ∀ a : T' ⟶ A, (tv ⟨x, φ, hφ⟩ t a z J * (tv ⟨x, φ', hφ'⟩ t a z J)⁻¹).val = gs t.left z ⊤ c := fun a => by
    have e₁ := val_pull_tv ⟨x, φ, hφ⟩ (snd A T) (fst A T) (lift a t) hJ
    have e₂ := val_pull_tv ⟨x, φ', hφ'⟩ (snd A T) (fst A T) (lift a t) hJ
    rw [lift_fst, lift_snd] at e₁ e₂
    have := hc _ (lift a t).left z J hJ
    rw [← Over.comp_left, lift_snd] at this
    rw [← e₁, ← e₂]
    exact this
  exact Units.ext ((key a).trans (key b).symm)

theorem CommV.congr (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T T₀ : Over S}
    {θx θy θx' θy' : ThetaGrp A L k T} {g : T ⟶ T₀} {c : Γ(T₀.left, ⊤)ˣ} (h : CommV θx θy g c)
    (hx : θx'.pt = θx.pt) (hy : θy'.pt = θy.pt) : CommV θx' θy' g c := by
  intro T' t a z J hJ
  have e₀ := congrArg Additive.ofMul (h T' t a z J hJ)
  have e₁ := congrArg Additive.ofMul (ratio_const hG hA hL θx' θx hx t a ((t ≫ θy.pt) * a) hJ)
  have e₂ := congrArg Additive.ofMul (ratio_const hG hA hL θy' θy hy t a ((t ≫ θx.pt) * a) hJ)
  rw [hx, hy]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at e₀ e₁ e₂ ⊢
  linear_combination (norm := abel) e₀ + e₁ - e₂

theorem CommV.restrict (hL : L.IsLB) {T T₀ T₁ : Over S}
    {θx θy : ThetaGrp A L k T} {g : T ⟶ T₀} {c : Γ(T₀.left, ⊤)ˣ} (h : CommV θx θy g c) (f : T₁ ⟶ T) :
    ∃ θx₁ θy₁ : ThetaGrp A L k T₁, θx₁.pt = f ≫ θx.pt ∧ θy₁.pt = f ≫ θy.pt ∧ CommV θx₁ θy₁ (f ≫ g) c := by
  obtain ⟨θx₁, px, vx⟩ := exists_restrict hL θx f
  obtain ⟨θy₁, py, vy⟩ := exists_restrict hL θy f
  refine ⟨θx₁, θy₁, px, py, fun T' t a z J hJ => ?_⟩
  rw [vx _ _ _ _ _ hJ, vx _ _ _ _ _ hJ, vy _ _ _ _ _ hJ, vy _ _ _ _ _ hJ, px, py, ← Category.assoc,
    ← Category.assoc, ← Category.assoc]
  exact h T' (t ≫ f) a z J hJ

theorem CommV.mul [IsCommMonObj A] (hL : L.IsLB) {T T₀ : Over S}
    {θx θx' θy : ThetaGrp A L k T} {g : T ⟶ T₀} {c c' : Γ(T₀.left, ⊤)ˣ} (h : CommV θx θy g c)
    (h' : CommV θx' θy g c') : ∃ θ : ThetaGrp A L k T, θ.pt = θx.pt * θx'.pt ∧ CommV θ θy g (c * c') := by
  obtain ⟨θ, p, v⟩ := exists_mul hL θx θx'
  refine ⟨θ, p, fun T' t a z J hJ => ?_⟩
  have e₀ := congrArg Additive.ofMul (h T' t a z J hJ)
  have e₁ := congrArg Additive.ofMul (h' T' t ((t ≫ θx.pt) * a) z J hJ)
  rw [v _ _ _ _ _ hJ, v _ _ _ _ _ hJ, p, MonObj.comp_mul, map_mul, mul_comm (t ≫ θx.pt) (t ≫ θx'.pt),
    _root_.mul_assoc (t ≫ θx'.pt), mul_left_comm (t ≫ θx.pt) (t ≫ θy.pt)]
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at e₀ e₁ ⊢
  linear_combination (norm := abel) e₀ + e₁

theorem exists_commV_of_le (hL : L.IsLB) {T : Over S} {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} {V W : T.left.Opens}
    (hle : W ≤ V)
    (h₁ : ∃ θx θy : ThetaGrp A L k (overRes V), θx.pt = overResι V ≫ x ∧ θy.pt = overResι V ≫ y)
    (h₂ : ∀ θx θy : ThetaGrp A L k (overRes V), θx.pt = overResι V ≫ x → θy.pt = overResι V ≫ y →
      CommIsOf A L k θx θy (unitRes V c)) :
    ∃ θx θy : ThetaGrp A L k (overRes W), θx.pt = overResι W ≫ x ∧ θy.pt = overResι W ≫ y ∧
      CommV θx θy (overResι W) c := by
  obtain ⟨θx, θy, px, py⟩ := h₁
  let f : overRes W ⟶ overRes V := Over.homMk (T.left.homOfLE hle) (by
    show T.left.homOfLE hle ≫ V.ι ≫ T.hom = W.ι ≫ T.hom
    rw [← Category.assoc, Scheme.homOfLE_ι])
  have hf : f ≫ overResι V = overResι W := Over.OverMorphism.ext (T.left.homOfLE_ι hle)
  obtain ⟨θx₁, θy₁, qx, qy, hc⟩ := ((commIs_iff hL V θx θy c).1 (h₂ θx θy px py)).restrict hL f
  refine ⟨θx₁, θy₁, ?_, ?_, hf ▸ hc⟩
  · rw [qx, px, ← Category.assoc, hf]
  · rw [qy, py, ← Category.assoc, hf]

end GlobalTheory.WeilMul

namespace GlobalTheory

open WeilMul in

theorem weilIs_mul_left : GlobalFnsSt → ∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S) (x x' y : T ⟶ P.A)
    (c c' : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k x' y c' →
      WeilIs P.A P.L k (x * x') y (c * c') := by
  intro hG S P k T x x' y c c' h h' p
  have := P.isAb.comm
  obtain ⟨V, hV, a₁, a₂⟩ := h p
  obtain ⟨V', hV', b₁, b₂⟩ := h' p
  obtain ⟨θx, θy, px, py, hc⟩ := exists_commV_of_le P.isLB (inf_le_left : V ⊓ V' ≤ V) a₁ a₂
  obtain ⟨θx', θy', px', py', hc'⟩ := exists_commV_of_le P.isLB (inf_le_right : V ⊓ V' ≤ V') b₁ b₂
  obtain ⟨θ, pθ, hθ⟩ := hc.mul P.isLB (hc'.congr hG P.isAb P.isLB rfl (py.trans py'.symm))
  have q : θ.pt = overResι (V ⊓ V') ≫ (x * x') := by rw [pθ, px, px', MonObj.comp_mul]
  refine ⟨V ⊓ V', ⟨hV, hV'⟩, ⟨θ, θy, q, py⟩, fun θ₁ θ₂ p₁ p₂ => ?_⟩
  exact (commIs_iff P.isLB _ _ _ _).2 (hθ.congr hG P.isAb P.isLB (p₁.trans q.symm) (p₂.trans py.symm))

end GlobalTheory
