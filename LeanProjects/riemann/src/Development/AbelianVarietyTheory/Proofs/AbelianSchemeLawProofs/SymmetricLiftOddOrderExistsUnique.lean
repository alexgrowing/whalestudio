import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymLiftOdd

theorem defect_pow {G U : Type} [CommGroup G] [CommGroup U] (f n : G → U) (X : G) (k : ℕ) (hX : X ^ k = 1)
    (α β : U) (hα : ∀ m, f (X⁻¹ * m) * n m * (f m⁻¹ * (n (X⁻¹ * m))⁻¹) = α)
    (hβ : ∏ j ∈ Finset.range k, f (X ^ j) = β) : α ^ k = β ^ 2 := by
  have h1 : ∏ j ∈ Finset.range k, f (X ^ (j + 1))⁻¹ = β := by
    rw [← hβ, ← Finset.prod_range_reflect (fun j => f (X ^ j)) k]
    refine Finset.prod_congr rfl fun j hj => congrArg f ?_
    have hj' := Finset.mem_range.1 hj
    rw [inv_eq_iff_mul_eq_one, ← pow_add, show j + 1 + (k - 1 - j) = k by omega, hX]
  have h2 : ∏ j ∈ Finset.range k, (n (X ^ (j + 1)) / n (X ^ j)) = 1 := by
    rw [Finset.prod_range_div (fun j => n (X ^ j)) k, hX, pow_zero, div_self']
  have h3 : ∀ j ∈ Finset.range k, α = f (X ^ j) * f (X ^ (j + 1))⁻¹ * (n (X ^ (j + 1)) / n (X ^ j)) := by
    intro j _
    rw [← hα (X ^ (j + 1)), pow_succ' X j, inv_mul_cancel_left, div_eq_mul_inv]
    ac_rfl
  calc α ^ k = ∏ _j ∈ Finset.range k, α := by rw [Finset.prod_const, Finset.card_range]
    _ = β ^ 2 := by
      rw [Finset.prod_congr rfl h3, Finset.prod_mul_distrib, Finset.prod_mul_distrib, hβ, h1, h2, _root_.mul_one, sq]

section General

variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem isGen_of_gm {t : LB.Gen (LB.LinComb L φ ε)}
    (h : ∀ (y : Y) (j j' : K → L.ι), y ∈ LB.wchart L φ j → y ∈ LB.wchart L φ j' →
      gm (𝟙 Y) y (LB.wchart L φ j) (t.s j) = trF φ ε (𝟙 Y) y j j' * gm (𝟙 Y) y (LB.wchart L φ j') (t.s j')) :
    t.IsGen := fun j j' => unit_ext fun y hy =>
  (gm_res (𝟙 Y) y _ hy _).trans ((h y j j' hy.1 hy.2).trans (Eq.symm ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L φ ε (𝟙 Y) y j j' hy.1 hy.2) (gm_res (𝟙 Y) y _ hy _)))))

theorem exists_const (hL : L.IsLB) {S₀ : Scheme.{0}} (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _)
    (hp : Function.Surjective p.appTop.hom)
    (hF : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = 1)
    {u : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) :
    ∃ a : Γ(S₀, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → val u r z J = gm (r ≫ p) z ⊤ a := by
  obtain ⟨t, -, hv⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ h => (hF U h).trans (Fintype.prod_empty _).symm) u hu
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ := hp (res le (t.s PEmpty.elim)).val
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z),
      (gm r z ⊤ (res le (t.s PEmpty.elim))).val = gs (r ≫ p) z ⊤ a := fun Z r z =>
    (gs_unit r z ⊤ trivial _).symm.trans ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a))
  refine ⟨pullU e ⊤ (res le (t.s PEmpty.elim)), fun Z r z J hJ => ?_⟩
  rw [← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  refine (gm_res r z le trivial _).symm.trans (Eq.trans ?_ (gm_pull (r ≫ p) e z ⊤ trivial _).symm)
  apply Units.ext
  rw [key, key, Category.assoc, he, Category.comp_id]

end General

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}

theorem surj_fst (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (T : Over S) :
    Function.Surjective (fst T A).left.appTop.hom := by
  have h1 : Function.Surjective (snd A T).left.appTop.hom := (hG _ _ (TLinPf.isAb_pullback T.hom A hA)).2
  have h2 : Function.Surjective (lift (snd T A) (fst T A)).left.appTop.hom := by
    have e : (lift (snd T A) (fst T A)).left ≫ (lift (snd A T) (fst A T)).left = 𝟙 _ :=
      congrArg (fun q => q.left) (show lift (snd T A) (fst T A) ≫ lift (snd A T) (fst A T) = 𝟙 _ by ext <;> simp)
    intro v
    refine ⟨(lift (snd A T) (fst A T)).left.appTop.hom v, ?_⟩
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e]
    simp
  have e : (fst T A).left = (lift (snd T A) (fst T A)).left ≫ (snd A T).left := by
    rw [← Over.comp_left, lift_snd]
  rw [e, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
  exact h2.comp h1

theorem exists_constT (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T : Over S} {K : Type} [Fintype K]
    {φ : K → ((T ⊗ A).left ⟶ A.left)} {ε : K → ℤ}
    (hF : ∀ (U : Type) [CommGroup U] (h : ((T ⊗ A).left ⟶ A.left) → U), ∏ k, h (φ k) ^ ε k = 1)
    {u : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) :
    ∃ a : Γ(T.left, ⊤)ˣ, ∀ (m : T ⊗ A ⟶ A) (y : (T ⊗ A).left) (J), Good L y J →
      val u (lift (fst T A) m).left y J = gm (fst T A).left y ⊤ a := by
  obtain ⟨a, ha⟩ := exists_const hL (fst T A).left (lift (𝟙 T) (1 : T ⟶ A)).left
    (by rw [← Over.comp_left, lift_fst]; rfl) (surj_fst hG hA T) hF hu
  exact ⟨a, fun m y J hJ => by rw [ha _ _ y J hJ, ← Over.comp_left, lift_fst]⟩

theorem lift_translT {T : Over S} (x : T ⟶ A) (m : T ⊗ A ⟶ A) :
    lift (fst T A) m ≫ translT A x = lift (fst T A) ((fst T A ≫ x) * m) := by
  rw [translT, translPt, comp_lift, lift_fst, comp_lift_assoc, lift_fst_assoc, lift_snd]; rfl

theorem lift_negT {T : Over S} (m : T ⊗ A ⟶ A) :
    lift (fst T A) m ≫ negT A T = lift (fst T A) m⁻¹ := by
  rw [negT, comp_lift, lift_fst, lift_snd_assoc]; rfl

theorem lift_translPt {T : Over S} (x : T ⟶ A) (m : T ⊗ A ⟶ A) :
    lift (fst T A) m ≫ translPt A x = (fst T A ≫ x) * m := by
  rw [translPt, comp_lift_assoc, lift_fst_assoc, lift_snd]; rfl

theorem translT_eq {T : Over S} (x : T ⟶ A) : translT A x = lift (fst T A) ((fst T A ≫ x) * snd T A) := rfl

theorem negT_eq (T : Over S) : negT A T = lift (fst T A) (snd T A)⁻¹ := rfl

theorem comp_pow' {T T' : Over S} (ρ : T' ⟶ T) (x : T ⟶ A) (n : ℕ) : ρ ≫ x ^ n = (ρ ≫ x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem comp_inv' {T T' : Over S} (ρ : T' ⟶ T) (x : T ⟶ A) : ρ ≫ x⁻¹ = (ρ ≫ x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one])

variable {T : Over S} {k : ℤ}

def thetaVal (θ : ThetaGrp A L k T) (y : (T ⊗ A).left) (J : ((T ⊗ A).left ⟶ A.left) → L.ι) (m : T ⊗ A ⟶ A) :
    ((T ⊗ A).left.presheaf.stalk y)ˣ :=
  val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (lift (fst T A) m).left y J

def negVal (nu : LB.Gen (negLB A L k T)) (y : (T ⊗ A).left) (J : ((T ⊗ A).left ⟶ A.left) → L.ι) (m : T ⊗ A ⟶ A) :
    ((T ⊗ A).left.presheaf.stalk y)ˣ :=
  val (L := L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) nu
    (lift (fst T A) m).left y J

theorem val_symGen (θ : ThetaGrp A L k T) (nu : LB.Gen (negLB A L k T)) {x : T ⟶ A} (hx : θ.pt = x)
    {y : (T ⊗ A).left} {J} (hJ : Good L y J) (m : T ⊗ A ⟶ A) :
    val (symGen A L k θ nu) (lift (fst T A) m).left y J =
      thetaVal θ y J ((fst T A ≫ x)⁻¹ * m) * negVal nu y J m *
        (thetaVal θ y J m⁻¹ * (negVal nu y J ((fst T A ≫ x)⁻¹ * m))⁻¹) := by
  subst hx
  have e₁ : (lift (fst T A) m).left ≫ (translT A θ.pt⁻¹).left = (lift (fst T A) ((fst T A ≫ θ.pt)⁻¹ * m)).left := by
    rw [← Over.comp_left, lift_translT, comp_inv']
  have e₂ : (lift (fst T A) m).left ≫ (negT A T).left = (lift (fst T A) m⁻¹).left := by
    rw [← Over.comp_left, lift_negT]
  refine (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_pull hJ _ _ _).trans ?_) rfl)) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_pull hJ _ _ _).trans ?_)
    ((val_inv _ _).trans (congrArg (·⁻¹) ((val_pull hJ _ _ _).trans ?_))))))
  · rw [e₁]; rfl
  · rw [e₂]; rfl
  · rw [e₁]; rfl

theorem gm_powGen (θ : ThetaGrp A L k T) (n : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    (j : Fin n × Fin 2 → L.ι) (hj : r z ∈ LB.wchart L (powφ A θ.pt n) j) :
    gm r z (LB.wchart L (powφ A θ.pt n) j) ((powGen A L k θ n).s j) =
      ∏ j₀ : Fin n, gm r z (LB.wchart L (fun b => (translT A (θ.pt ^ (j₀ : ℕ))).left ≫
            (![(snd T A).left, (translPt A θ.pt).left] b)) (fun b => j (j₀, b)))
        ((LB.pullGen L ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] θ.φ
          (translT A (θ.pt ^ (j₀ : ℕ))).left).s (fun b => j (j₀, b))) := by
  unfold powGen
  refine (map_prod (gm r z (LB.wchart L (powφ A θ.pt n) j)) _ (Finset.univ : Finset (Fin n))).trans
    (Finset.prod_congr rfl fun j₀ _ => ?_)
  exact gm_res r z (V := LB.wchart L (powφ A θ.pt n) j) _ hj _

theorem powGen_isGen (θ : ThetaGrp A L k T) (n : ℕ) : (powGen A L k θ n).IsGen := by
  refine isGen_of_gm fun y j j' hj hj' => ?_
  rw [gm_powGen θ n (𝟙 _) y j hj, gm_powGen θ n (𝟙 _) y j' hj', trF, Fintype.prod_prod_type,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j₀ _ => gen_trans (DVR.pullGen_isGen L _ _ _ θ.isGen _) (𝟙 _) y
    (Set.mem_iInter.2 fun b => Set.mem_iInter.1 hj (j₀, b)) (Set.mem_iInter.2 fun b => Set.mem_iInter.1 hj' (j₀, b))

theorem val_powGen (θ : ThetaGrp A L k T) (n : ℕ) {x : T ⟶ A} (hx : θ.pt = x)
    {y : (T ⊗ A).left} {J} (hJ : Good L y J) (m : T ⊗ A ⟶ A) :
    val (powGen A L k θ n) (lift (fst T A) m).left y J =
      ∏ j ∈ Finset.range n, thetaVal θ y J ((fst T A ≫ x) ^ j * m) := by
  subst hx
  rw [Finset.prod_range]
  refine (gm_powGen θ n _ y _ (hJ.mem _ _)).trans (Finset.prod_congr rfl fun j₀ _ => ?_)
  refine (val_pull hJ (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
    (translT A (θ.pt ^ (j₀ : ℕ))).left (lift (fst T A) m).left).trans ?_
  rw [← Over.comp_left, lift_translT, comp_pow']; rfl

theorem form_pow {n : ℕ} {x : T ⟶ A} (hx : x ^ n = 1) (U : Type) [CommGroup U] (h : ((T ⊗ A).left ⟶ A.left) → U) :
    ∏ p, h (powφ A x n p) ^ powε k n p = 1 := by
  let g : ℕ → U := fun j => h ((fst T A ≫ x) ^ j * snd T A).left ^ (-k)
  have e : ∀ j : Fin n, ∏ b : Fin 2, h (powφ A x n (j, b)) ^ powε k n (j, b) = g (j + 1) / g j := fun j => by
    rw [Fin.prod_univ_two]
    show h (translT A (x ^ (j : ℕ)) ≫ snd T A).left ^ k * h (translT A (x ^ (j : ℕ)) ≫ translPt A x).left ^ (-k) = _
    rw [translT_eq, lift_snd, lift_translPt, comp_pow', ← _root_.mul_assoc, ← pow_succ', div_eq_mul_inv, mul_comm]
    simp only [g, zpow_neg, inv_inv]
  rw [Fintype.prod_prod_type, Finset.prod_congr rfl fun j _ => e j, ← Finset.prod_range (fun j => g (j + 1) / g j),
    Finset.prod_range_div]
  simp only [g]
  rw [← comp_pow', hx, MonObj.comp_one, pow_zero, div_self']

theorem symGen_isGen (θ : ThetaGrp A L k T) {nu : LB.Gen (negLB A L k T)} (hnu : nu.IsGen) :
    (symGen A L k θ nu).IsGen :=
  DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ θ.isGen _) hnu)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ θ.isGen _)
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hnu _)))

theorem exists_symConst (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) (θ : ThetaGrp A L k T)
    {nu : LB.Gen (negLB A L k T)} (hnu : nu.IsGen) :
    ∃ a : Γ(T.left, ⊤)ˣ, ∀ (m : T ⊗ A ⟶ A) (y : (T ⊗ A).left) (J), Good L y J →
      val (symGen A L k θ nu) (lift (fst T A) m).left y J = gm (fst T A).left y ⊤ a := by
  have := hA.comm
  refine exists_constT hG hA hL (fun U _ h => ?_) (symGen_isGen θ hnu)
  simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
    Matrix.cons_val_one, ← Over.comp_left]
  have e : snd T A ≫ (GrpObj.inv : A ⟶ A) = (snd T A)⁻¹ := rfl
  rw [e, translT_eq, negT_eq, comp_inv', comp_inv', lift_snd, lift_snd, lift_translPt, lift_translPt,
    mul_inv_cancel_left, mul_inv, inv_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_one]
  module

theorem exists_scale (hL : L.IsLB) (θ : ThetaGrp A L k T) (c : Γ(T.left, ⊤)ˣ) :
    ∃ θ' : ThetaGrp A L k T, θ'.pt = θ.pt ∧ ∀ y J, Good L y J → ∀ m,
      thetaVal θ' y J m = thetaVal θ y J m * gm (fst T A).left y ⊤ c := by
  have vc : ∀ {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) (j : PEmpty → L.ι),
      gm r z (LB.wchart L PEmpty.elim j) ((constGen A L c).s j) = gm (r ≫ (fst T A).left) z ⊤ c := fun r z j =>
    (gm_res r z _ (Set.mem_iInter.2 fun k => k.elim) _).trans (gm_pull r _ z ⊤ trivial c)
  have hc : (constGen A L c).IsGen := isGen_of_gm fun y j j' _ _ => by
    rw [vc, vc, trF, Fintype.prod_empty, _root_.one_mul]
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (translPt A θ.pt).left]) (ε' := ![k, -k])
    (fun U _ h => (Fintype.prod_sum_type _).trans ((congrArg₂ (· * ·) rfl (Finset.prod_eq_one fun (i : PEmpty) _ => i.elim)).trans
      (_root_.mul_one _)))
    (LB.mulGen L ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] _ _ θ.φ (constGen A L c))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ θ.isGen hc)
  refine ⟨⟨θ.pt, t, ht⟩, rfl, fun y J hJ m => (hv _ _ y J hJ).trans ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl ((vc _ y _).trans ?_)))⟩
  rw [← Over.comp_left, lift_fst]

theorem exists_ratio (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → ((T ⊗ A).left ⟶ A.left)} {ε : K → ℤ} {u u' : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ c : Γ(T.left, ⊤)ˣ, ∀ (m : T ⊗ A ⟶ A) (y : (T ⊗ A).left) (J), Good L y J →
      val u (lift (fst T A) m).left y J = val u' (lift (fst T A) m).left y J * gm (fst T A).left y ⊤ c := by
  obtain ⟨c, hc⟩ := exists_constT hG hA hL (fun U _ h => (Fintype.prod_sum_type _).trans (by
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel]))
    (DVR.mulGen_isGen L _ _ _ _ u (LB.invGen L _ _ u') hu (DVR.invGen_isGen _ _ _ _ hu'))
  refine ⟨c, fun m y J hJ => ?_⟩
  rw [← hc m y J hJ, val_mul hJ, val_inv, mul_comm, inv_mul_cancel_right]

theorem id_eq_lift : 𝟙 (T ⊗ A).left = (lift (fst T A) (snd T A)).left := by rw [lift_fst_snd]; rfl

theorem exists_symLift (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {n : ℕ} (hn : Odd n) {x : T ⟶ A}
    (hx : x ^ n = 1) (θ : ThetaGrp A L k T) (hθ : θ.pt = x) {nu : LB.Gen (negLB A L k T)} (hnu : nu.IsGen) :
    ∃ θ' : ThetaGrp A L k T, SymLift A L k n x θ' := by
  have := hA.comm
  obtain ⟨a, ha⟩ := exists_symConst hG hA hL θ hnu
  obtain ⟨b, hb⟩ := exists_constT hG hA hL (form_pow (k := k) (hθ ▸ hx : θ.pt ^ n = 1)) (powGen_isGen θ n)
  have hab : ∀ y J, Good L y J → gm (fst T A).left y ⊤ a ^ n = gm (fst T A).left y ⊤ b ^ 2 := fun y J hJ =>
    defect_pow (thetaVal θ y J) (negVal nu y J) (fst T A ≫ x) n (by rw [← comp_pow', hx, MonObj.comp_one]) _ _
      (fun m => (val_symGen θ nu hθ hJ m).symm.trans (ha m y J hJ)) (by
        rw [← hb 1 y J hJ, val_powGen θ n hθ hJ]; simp only [_root_.mul_one])
  obtain ⟨l, rfl⟩ := hn
  obtain ⟨θ', hpt, hv⟩ := exists_scale hL θ (b⁻¹ * a ^ l)
  have hθ' : θ'.pt = x := hpt.trans hθ
  refine ⟨θ', hθ', corr_of_val hL fun y J hJ => ?_, nu, hnu, corr_of_val hL fun y J hJ => ?_⟩
  · rw [val_one, id_eq_lift, val_powGen θ' _ hθ' hJ, Finset.prod_congr rfl fun j _ => hv y J hJ _,
      Finset.prod_mul_distrib, ← val_powGen θ _ hθ hJ, hb _ y J hJ, Finset.prod_const, Finset.card_range, map_mul,
      map_inv, map_pow, mul_pow, ← pow_mul, mul_comm l, pow_mul, hab y J hJ]
    generalize gm (fst T A).left y ⊤ b = β
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one]
    module
  · have e₁ := (val_symGen θ nu hθ hJ (snd T A)).symm.trans (ha _ y J hJ)
    have e₂ := hab y J hJ
    rw [val_one, id_eq_lift, val_symGen θ' nu hθ' hJ, hv y J hJ, hv y J hJ, map_mul, map_inv, map_pow]
    apply Additive.ofMul.injective
    replace e₁ := congrArg Additive.ofMul e₁
    replace e₂ := congrArg Additive.ofMul e₂
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one] at e₁ e₂ ⊢
    linear_combination (norm := module) e₁ + e₂

theorem symLift_unique (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {n : ℕ} (hn : Odd n) {x : T ⟶ A}
    (θ θ' : ThetaGrp A L k T) (h : SymLift A L k n x θ) (h' : SymLift A L k n x θ') :
    LB.Gen.Corr L _ _ _ _ θ.φ θ'.φ := by
  obtain ⟨p, φ, hφ⟩ := θ
  obtain ⟨p', φ', hφ'⟩ := θ'
  obtain rfl : p = x := h.pt_eq
  obtain rfl : p' = p := h'.pt_eq
  obtain ⟨nu, hnu, hs⟩ := h.sym
  obtain ⟨nu', hnu', hs'⟩ := h'.sym
  obtain ⟨c, hc⟩ := exists_ratio hG hA hL hφ hφ'
  obtain ⟨d, hd⟩ := exists_ratio hG hA hL hnu hnu'
  refine corr_of_val hL fun y J hJ => ?_
  have hc' : ∀ m, thetaVal ⟨p', φ, hφ⟩ y J m = thetaVal ⟨p', φ', hφ'⟩ y J m * gm (fst T A).left y ⊤ c :=
    fun m => hc m y J hJ
  have hd' : ∀ m, negVal nu y J m = negVal nu' y J m * gm (fst T A).left y ⊤ d := fun m => hd m y J hJ
  have s₁ := (val_symGen _ nu rfl hJ (snd T A)).symm.trans ((val_corr hJ hs _).trans (val_one _))
  have s₂ := (val_symGen _ nu' rfl hJ (snd T A)).symm.trans ((val_corr hJ hs' _).trans (val_one _))
  have q₁ := (val_powGen _ n rfl hJ (snd T A)).symm.trans ((val_corr hJ h.pow_eq _).trans (val_one _))
  have q₂ := (val_powGen _ n rfl hJ (snd T A)).symm.trans ((val_corr hJ h'.pow_eq _).trans (val_one _))
  rw [Finset.prod_congr rfl fun j _ => hc' _, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range] at q₁
  rw [hc', hc', hd', hd'] at s₁
  have c2 : gm (fst T A).left y ⊤ c ^ 2 = 1 := by
    apply Additive.ofMul.injective
    replace s₁ := congrArg Additive.ofMul s₁
    replace s₂ := congrArg Additive.ofMul s₂
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one] at s₁ s₂ ⊢
    linear_combination (norm := module) s₁ - s₂
  have cn : gm (fst T A).left y ⊤ c ^ n = 1 := (_root_.one_mul _).symm.trans ((congrArg (· * _) q₂.symm).trans q₁)
  obtain ⟨l, rfl⟩ := hn
  rw [pow_succ, pow_mul, c2, one_pow, _root_.one_mul] at cn
  have := hc (snd T A) y J hJ
  rw [cn, _root_.mul_one, ← id_eq_lift] at this
  exact this

end GlobalTheory.SymLiftOdd

namespace GlobalTheory

theorem symLift_odd : GlobalFnsSt → (∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A), x ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp P.A P.L N (overRes V), θ.pt = overResι V ≫ x) → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℤ) (T : Over S), ∃ nu : LB.Gen (negLB P.A P.L k T), nu.IsGen) → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ), Odd k → ∀ (T : Over S) (x : T ⟶ P.A), x ^ k = 1 → (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp P.A P.L k (overRes V), SymLift P.A P.L k k (overResι V ≫ x) θ) ∧ ∀ θ θ' : ThetaGrp P.A P.L k T, SymLift P.A P.L k k x θ → SymLift P.A P.L k k x θ' → LB.Gen.Corr P.L _ _ _ _ θ.φ θ'.φ) ∧ SymLiftSt := by
  intro hG hlift hneg
  have main : ∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ), Odd k → ∀ (T : Over S) (x : T ⟶ P.A), x ^ k = 1 →
      (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
        ∃ θ : ThetaGrp P.A P.L k (overRes V), SymLift P.A P.L k k (overResι V ≫ x) θ) ∧
      ∀ θ θ' : ThetaGrp P.A P.L k T, SymLift P.A P.L k k x θ → SymLift P.A P.L k k x θ' →
        LB.Gen.Corr P.L _ _ _ _ θ.φ θ'.φ := by
    intro S P k hk T x hx
    refine ⟨fun p => ?_, fun θ θ' => SymLiftOdd.symLift_unique hG P.isAb P.isLB hk θ θ'⟩
    obtain ⟨V, hV, θ, hθ⟩ := hlift S P k T x hx p
    obtain ⟨nu, hnu⟩ := hneg S P k (overRes V)
    exact ⟨V, hV, SymLiftOdd.exists_symLift hG P.isAb P.isLB hk
      (by rw [← SymLiftOdd.comp_pow', hx, MonObj.comp_one]) θ hθ hnu⟩
  exact ⟨main, fun S _ P k hk _ => main S P k hk⟩

end GlobalTheory
