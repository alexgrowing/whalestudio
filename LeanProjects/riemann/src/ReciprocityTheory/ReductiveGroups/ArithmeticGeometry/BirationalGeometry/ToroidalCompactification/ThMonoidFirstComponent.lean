import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

section Alg

variable {A U : Type} [CommGroup A] [CommGroup U]

variable (A U) in

@[ext] structure Th where

  x : A

  f : A → U

instance : Monoid (Th A U) where
  mul g h := ⟨g.x * h.x, fun y => g.f y * h.f (y * g.x)⟩
  one := ⟨1, fun _ => 1⟩
  mul_assoc g h k := Th.ext (_root_.mul_assoc _ _ _) (funext fun y => by
    show g.f y * h.f (y * g.x) * k.f (y * (g.x * h.x)) = g.f y * (h.f (y * g.x) * k.f (y * g.x * h.x))
    rw [_root_.mul_assoc, _root_.mul_assoc y])
  one_mul g := Th.ext (_root_.one_mul _) (funext fun y => by show 1 * g.f (y * 1) = _; rw [_root_.one_mul, _root_.mul_one])
  mul_one g := Th.ext (_root_.mul_one _) (funext fun y => _root_.mul_one _)

theorem Th.adapted_frame_mul_vecMulVec (g h : Th A U) : (g * h).x = g.x * h.x := rfl
theorem Th.mul_f (g h : Th A U) (y : A) : (g * h).f y = g.f y * h.f (y * g.x) := rfl

theorem Th.theta_pow_x (g : Th A U) (n : ℕ) : (g ^ n).x = g.x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ n ih => rw [pow_succ, pow_succ, Th.adapted_frame_mul_vecMulVec, ih]

theorem Th.pow_f (g : Th A U) (n : ℕ) (y : A) : (g ^ n).f y = ∏ j ∈ Finset.range n, g.f (y * g.x ^ j) := by
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih => rw [pow_succ, Th.mul_f, ih, Th.theta_pow_x, Finset.prod_range_succ]

structure Th.Sym (ν : A → U) (N : ℕ) (g : Th A U) : Prop where
  pow : g ^ N = 1
  sym : ∀ y, g.f (y * g.x⁻¹) * ν y * g.f y⁻¹ = ν (y * g.x⁻¹)

variable {ν ν' : A → U} {N : ℕ} {g h : Th A U}

theorem Th.Sym.of_dvd {N' : ℕ} (s : g.Sym ν N) (d : N ∣ N') : g.Sym ν N' := ⟨by obtain ⟨r, rfl⟩ := d; rw [pow_mul, s.pow, one_pow], s.sym⟩

theorem Th.Sym.mul (s : g.Sym ν N) (t : h.Sym ν N) (c : Commute g h) : (g * h).Sym ν N := by
  refine ⟨by rw [c.mul_pow, s.pow, t.pow, _root_.mul_one], fun y => ?_⟩
  have a₁ := congrArg Additive.ofMul (s.sym y)
  have a₂ := congrArg Additive.ofMul (t.sym (y * g.x⁻¹))
  have a₃ := congrArg (fun q : Th A U => Additive.ofMul (q.f (y * g.x⁻¹ * h.x⁻¹))) c.eq
  have e₁ : y * (g.x * h.x)⁻¹ = y * g.x⁻¹ * h.x⁻¹ := by rw [mul_inv, _root_.mul_assoc]
  have e₂ : (y * g.x⁻¹)⁻¹ = y⁻¹ * g.x := by rw [mul_inv, inv_inv]
  apply Additive.ofMul.injective
  simp only [Th.mul_f, Th.adapted_frame_mul_vecMulVec, e₁, e₂, inv_mul_cancel_right, ofMul_mul] at a₁ a₂ a₃ ⊢
  linear_combination (norm := abel) a₁ + a₂ + a₃

theorem Th.Sym.unique (hN : Odd N) (s : g.Sym ν N) (t : h.Sym ν N) (ex : g.x = h.x) {c : U} (e : ∀ y, g.f y = c * h.f y) :
    g = h := by
  have p : c ^ N = 1 := by
    have a := congrArg (fun q : Th A U => q.f 1) s.pow
    have b := congrArg (fun q : Th A U => q.f 1) t.pow
    simp only [Th.pow_f, e, ex, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range] at a b
    rw [b] at a; exact (_root_.mul_one _).symm.trans a
  have q : c ^ 2 = 1 := by
    have a := congrArg Additive.ofMul (s.sym 1)
    have b := congrArg Additive.ofMul (t.sym 1)
    apply Additive.ofMul.injective
    simp only [e, ex, ofMul_mul, ofMul_pow, ofMul_one] at a b ⊢
    linear_combination (norm := abel) a - b
  obtain ⟨m, rfl⟩ := hN
  rw [pow_succ, pow_mul, q, one_pow, _root_.one_mul] at p
  exact Th.ext ex (funext fun y => by rw [e, p, _root_.one_mul])

def Th.pull (f : A →* A) (δ : A → U) (x : A) (g : Th A U) : Th A U := ⟨x, fun y => δ y * g.f (f y) * (δ (y * x))⁻¹⟩

theorem Th.Sym.pull (s : g.Sym ν N) (f : A →* A) (δ : A → U) {x : A} (hx : f x = g.x) (hN : x ^ N = 1) {κ : U}
    (hν : ∀ y, ν' y = κ * (δ y * (δ y⁻¹)⁻¹ * ν (f y))) : (g.pull f δ x).Sym ν' N := by
  have tel : ∀ n y, ((g.pull f δ x) ^ n).f y = δ y * (g ^ n).f (f y) * (δ (y * x ^ n))⁻¹ := fun n y => by
    induction n with
    | zero => rw [pow_zero, pow_zero, pow_zero, _root_.mul_one]; show 1 = δ y * 1 * _; simp
    | succ n ih =>
      rw [pow_succ, pow_succ g, Th.mul_f, Th.mul_f, ih, Th.theta_pow_x, Th.theta_pow_x, pow_succ, ← _root_.mul_assoc y, ← hx, ← map_pow,
        ← map_mul]
      apply Additive.ofMul.injective
      simp only [Th.pull, ofMul_mul, ofMul_inv]
      abel
  refine ⟨Th.ext ((Th.theta_pow_x _ _).trans hN) (funext fun y => ?_), fun y => ?_⟩
  · rw [tel, s.pow, hN, _root_.mul_one]; show δ y * 1 * _ = 1; simp
  · have a := congrArg Additive.ofMul (s.sym (f y))
    have e₂ : (y * x⁻¹)⁻¹ = y⁻¹ * x := by rw [mul_inv, inv_inv]
    apply Additive.ofMul.injective
    simp only [Th.pull, hν, e₂, inv_mul_cancel_right, map_mul, map_inv, hx, ofMul_mul, ofMul_inv] at a ⊢
    linear_combination (norm := abel) a

theorem Th.sym_one : (1 : Th A U).Sym ν N := ⟨one_pow _, fun y => by show 1 * ν y * 1 = ν (y * 1⁻¹); simp⟩

theorem Th.commute_of {θ : A → A → A → U} (C : IsCub θ) {k : ℕ} (hg : g.x ^ k = 1) (hh : h.x ^ k = 1)
    (eg : ∀ y, g.f y = g.f 1 * cubN θ k 1 g.x y) (eh : ∀ y, h.f y = h.f 1 * cubN θ k 1 h.x y)
    (e : cubN θ k 1 g.x h.x = cubN θ k 1 h.x g.x) : Commute g h :=
  Th.ext (mul_comm _ _) (funext fun y => by
    have a₁ := congrArg Additive.ofMul (cubN_right C hg y h.x)
    have a₂ := congrArg Additive.ofMul (cubN_right C hh y g.x)
    have a₃ := congrArg Additive.ofMul e
    rw [C.s01, C.s12, C.s01] at a₂
    rw [Th.mul_f, Th.mul_f, eg y, eh y, eg (y * _), eh (y * _)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul] at a₁ a₂ a₃ ⊢
    linear_combination (norm := abel) a₂ - a₁ - a₃)

end Alg

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} {T T' : Over S} (σ : T' ⟶ T) (z : T'.left)
  (J : (T'.left ⟶ A.left) → L.L.ι)

def IsGeo (k : ℕ) (x : T ⟶ A) (g : Th (T' ⟶ A) (T'.left.presheaf.stalk z)ˣ) : Prop :=
  g.x = σ ≫ x ∧ ∃ (K : Type) (_ : Fintype K) (φ : K → ((T ⊗ A).left ⟶ A.left)) (ε : K → ℤ) (u : LB.Gen (LB.LinComb L.L φ ε)),
    u.IsGen ∧ (∀ (U : Type) [CommGroup U] (h : ((T ⊗ A).left ⟶ A.left) → U), ∏ i, h (φ i) ^ ε i =
      h (snd T A).left ^ k * (h ((fst T A ≫ x) * snd T A).left ^ k)⁻¹) ∧ ∀ y, val u (lift σ y).left z J = g.f y

variable {σ z J} (hJ : Good L.L z J) {k : ℕ} {x x' : T ⟶ A} {g g' : Th (T' ⟶ A) (T'.left.presheaf.stalk z)ˣ}
include hJ

theorem IsGeo.cub (c : CubicalStr A L) (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (h : IsGeo σ z J k x g) (hx : x ^ k = 1) (y) :
    g.f y = g.f 1 * cubN (cubV c z J) k 1 g.x y := by
  obtain ⟨e, K, _, φ, ε, u, hu, hF, v⟩ := h
  rw [← v, ← v, e]; exact val_theta c hG hA hx u hu hF σ y hJ

theorem IsGeo.mul (h : IsGeo σ z J k x g) (h' : IsGeo σ z J k x' g') : IsGeo σ z J k (x * x') (g * g') := by
  obtain ⟨e, K, _, φ, ε, u, hu, hF, v⟩ := h
  obtain ⟨e', K', _, φ', ε', u', hu', hF', v'⟩ := h'
  refine ⟨by rw [Th.adapted_frame_mul_vecMulVec, e, e', MonObj.comp_mul], _, inferInstance, _, _,
    LB.mulGen L.L _ _ _ _ u (LB.pullGen L.L _ _ u' (translT A x).left),
    mulGen_isGen _ _ _ _ _ _ _ hu (pullGen_isGen _ _ _ _ hu' _), fun U _ h => ?_, fun y => ?_⟩
  · refine (prod_sum₂ (K := K) (K' := K') (U := U) _ (hF U h) (hF' U fun q => h ((translT A x).left ≫ q))).trans ?_
    have a : translT A x ≫ snd T A = (fst T A ≫ x) * snd T A := lift_snd _ _
    have b : translT A x ≫ fst T A = fst T A := lift_fst _ _
    simp only [← Over.comp_left, MonObj.comp_mul, ← Category.assoc, a, b]
    rw [mul_left_comm (fst T A ≫ x'), ← _root_.mul_assoc (fst T A ≫ x), _root_.mul_assoc, inv_mul_cancel_left]
  · rw [val_mul hJ, val_pull hJ, ← Over.comp_left, lift_transl, v, v', Th.mul_f, e, mul_comm y]

theorem IsGeo.pull {a : ℕ} (f : A ⟶ A) [IsMonHom f] (h : IsGeo σ z J a (x ≫ f) g) {K₀ : Type} [Fintype K₀]
    {φ₀ : K₀ → (A.left ⟶ A.left)} {ε₀ : K₀ → ℤ} (δ : LB.Gen (LB.LinComb L.L φ₀ ε₀)) (hδ : δ.IsGen)
    (hF₀ : ∀ {T : Over S} (y : T ⟶ A) (U : Type) [CommGroup U] (h : (T.left ⟶ A.left) → U), ∏ i, h (y.left ≫ φ₀ i) ^ ε₀ i =
      h y.left ^ k * (h (y ≫ f).left ^ a)⁻¹) :
    IsGeo σ z J k x (g.pull (MonoidHom.mk' (· ≫ f) fun p q => MonObj.mul_comp p q f) (fun y => val δ y.left z J) (σ ≫ x)) := by
  obtain ⟨e, K, _, φ, ε, u, hu, hF, v⟩ := h
  let n : T ⊗ A ⟶ T ⊗ A := lift (fst T A) (snd T A ≫ f)
  refine ⟨rfl, _, inferInstance, _, _, LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ δ (snd T A).left)
    (LB.pullGen L.L _ _ u n.left)) (LB.invGen L.L _ _ (LB.pullGen L.L _ _ δ ((fst T A ≫ x) * snd T A).left)),
    mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hδ _) (pullGen_isGen _ _ _ _ hu _))
      (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hδ _)), fun U _ h => ?_, fun y => ?_⟩
  · refine (prod_sum₂ (K := K₀ ⊕ K) (K' := K₀) (U := U) _ (prod_sum₂ (K := K₀) (K' := K) (U := U) _ (hF₀ _ U h)
      (hF U fun q => h (n.left ≫ q))) (prod_neg _ _ (hF₀ _ U h))).trans ?_
    simp only [← Over.comp_left, MonObj.comp_mul, MonObj.mul_comp, n, lift_snd, lift_fst_assoc, Category.assoc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · rw [val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left,
      ← Over.comp_left, lift_snd, MonObj.comp_mul, lift_fst_assoc, lift_snd, comp_lift, lift_fst, lift_snd_assoc, v, mul_comm (σ ≫ x)]
    rfl

omit hJ in
theorem isGeo_one : IsGeo (L := L) σ z J k 1 1 :=
  ⟨(MonObj.comp_one σ).symm, PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, LB.oneGen L.L, fun i j => (map_one _).trans
    ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm, fun U _ h => by
      rw [MonObj.comp_one, _root_.one_mul]; simp, fun _ => val_one _⟩

theorem nu_pull (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {K₁ : Type} [Fintype K₁] {φ₁ : K₁ → (A.left ⟶ A.left)} {ε₁ : K₁ → ℤ}
    (ν : LB.Gen (LB.LinComb L.L φ₁ ε₁)) (hν : ν.IsGen)
    (hF₁ : ∀ {T : Over S} (y : T ⟶ A) (U : Type) [CommGroup U] (h : (T.left ⟶ A.left) → U), ∏ i, h (y.left ≫ φ₁ i) ^ ε₁ i =
      h y.left * (h y⁻¹.left)⁻¹) {a : ℕ} (f : A ⟶ A) [IsMonHom f] {K₀ : Type} [Fintype K₀]
    {φ₀ : K₀ → (A.left ⟶ A.left)} {ε₀ : K₀ → ℤ} (δ : LB.Gen (LB.LinComb L.L φ₀ ε₀)) (hδ : δ.IsGen)
    (hF₀ : ∀ {T : Over S} (y : T ⟶ A) (U : Type) [CommGroup U] (h : (T.left ⟶ A.left) → U), ∏ i, h (y.left ≫ φ₀ i) ^ ε₀ i =
      h y.left ^ k * (h (y ≫ f).left ^ a)⁻¹) : ∃ κ, ∀ y : T' ⟶ A, val ν y.left z J ^ k =
      κ * (val δ y.left z J * (val δ y⁻¹.left z J)⁻¹ * val ν (y ≫ f).left z J ^ a) := by
  have pw : ∀ (n : ℕ) (y : T' ⊗ A ⟶ A) (U : Type) [CommGroup U] (h : ((T' ⊗ A).left ⟶ A.left) → U),
      ∏ i, h (y.left ≫ φ₁ i) ^ ((n : ℤ) * ε₁ i) = (h y.left * (h y⁻¹.left)⁻¹) ^ n := fun n y U _ h => by
    rw [← hF₁ y U h, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => by rw [mul_comm, zpow_mul, zpow_natCast]
  let P : ∀ (n : ℕ) (y : T' ⊗ A ⟶ A), LB.Gen (LB.LinComb L.L (fun i => y.left ≫ φ₁ i) fun i => (n : ℤ) * ε₁ i) :=
    fun n y => ⟨fun j => (LB.pullGen L.L _ _ ν y.left).s j ^ n⟩
  have vP : ∀ n y (r : T'.left ⟶ _), val (P n y) r z J = val ν (r ≫ y.left) z J ^ n := fun n y r =>
    (map_pow _ _ _).trans (congrArg (· ^ n) (val_pull hJ ν y.left r))
  have gP : ∀ n y, (P n y).IsGen := fun n y => isGen_of_gm _ fun w j j' h h' => (map_pow _ _ _).trans
    ((congrArg (· ^ n) (gen_trans (pullGen_isGen _ _ _ _ hν y.left) (𝟙 _) w h h')).trans ((mul_pow _ _ _).trans
      (congrArg₂ (· * ·) (by
        rw [trF, trF, ← Finset.prod_pow]
        exact Finset.prod_congr rfl fun i _ => by rw [mul_comm, zpow_mul, zpow_natCast]) (map_pow _ _ _).symm)))
  have key := fun y => ratio_const hG hA L.isLB (fun U _ h => by
      refine (prod_sum₂ (K := K₀ ⊕ K₀) (K' := K₁) (U := U) _ (prod_sum₂ (K := K₀) (K' := K₀) (U := U) _ (hF₀ (snd T' A) U h)
        (prod_neg _ _ (hF₀ (snd T' A)⁻¹ U h))) (pw a (snd T' A ≫ f) U h)).trans (Eq.trans ?_ (pw k (snd T' A) U h).symm)
      rw [GrpObj.inv_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow]
      module) (gP k (snd T' A)) (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hδ (snd T' A).left)
        (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hδ (snd T' A)⁻¹.left))) (gP a (snd T' A ≫ f))) (𝟙 T') y hJ
  exact ⟨_, fun y => ((vP k _ _).trans (by rw [← Over.comp_left, lift_snd])).symm.trans ((eq_mul_inv_of_mul_eq (key y)).trans
    ((_root_.mul_assoc _ _ _).trans ((mul_comm _ _).trans (congrArg₂ (· * ·) rfl (by
      rw [val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, vP, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left,
        lift_snd, GrpObj.comp_inv, lift_snd, lift_snd_assoc])))))⟩

theorem symLift_geo (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {K₁ : Type} [Fintype K₁] {φ₁ : K₁ → (A.left ⟶ A.left)}
    {ε₁ : K₁ → ℤ} (ν : LB.Gen (LB.LinComb L.L φ₁ ε₁)) (hν : ν.IsGen)
    (hF₁ : ∀ {T : Over S} (y : T ⟶ A) (U : Type) [CommGroup U] (h : (T.left ⟶ A.left) → U), ∏ i, h (y.left ≫ φ₁ i) ^ ε₁ i =
      h y.left * (h y⁻¹.left)⁻¹) {kz : ℤ} (hk : kz = k) {n : ℕ} {W : ThetaGrp A L.L kz T} (h : SymLift A L.L kz n x W)
    (hn : x ^ n = 1) : IsGeo σ z J k x ⟨σ ≫ x, fun y => val (L := L.L) (φ := ![(snd T A).left, (translPt A W.pt).left])
      (ε := ![kz, -kz]) W.φ (lift σ y).left z J⟩ ∧ Th.Sym (fun y => val ν y.left z J ^ k) n ⟨σ ≫ x, fun y =>
      val (L := L.L) (φ := ![(snd T A).left, (translPt A W.pt).left]) (ε := ![kz, -kz]) W.φ (lift σ y).left z J⟩ := by
  subst hk
  obtain rfl := h.pt_eq
  refine ⟨⟨rfl, Fin 2, inferInstance, _, _, W.φ, W.isGen, fun U _ h => ?_, fun _ => rfl⟩, Th.ext ?_ (funext fun y => ?_), fun y => ?_⟩
  · rw [Fin.prod_univ_two]
    show h _ ^ (k : ℤ) * h _ ^ (-(k : ℤ)) = _
    rw [zpow_neg, zpow_natCast, zpow_natCast]; rfl
  · exact (Th.theta_pow_x _ _).trans ((MonObj.comp_pow _ _ _).symm.trans (by rw [hn, MonObj.comp_one]; rfl))
  · have e := (val_corr hJ h.pow_eq (lift σ y).left).trans (val_one _)
    have hz := hJ.mem (powφ A W.pt n) (lift σ y).left
    rw [Th.pow_f, ← Fin.prod_univ_eq_prod_range (fun j => val (L := L.L) (φ := ![(snd T A).left, (translPt A W.pt).left])
      (ε := ![(k : ℤ), -(k : ℤ)]) W.φ (lift σ (y * (σ ≫ W.pt) ^ j)).left z J)]
    refine Eq.trans (Finset.prod_congr rfl fun j _ => ?_) ((map_prod _ _ _).symm.trans e)
    refine Eq.trans ?_ ((gm_res _ z _ hz _).trans (val_pull hJ W.φ (translT A (W.pt ^ (j : ℕ))).left (lift σ y).left)).symm
    rw [← Over.comp_left, lift_transl, mul_comm, MonObj.comp_pow]
  · obtain ⟨mu, hmu, hs⟩ := h.sym
    have e := (val_corr hJ hs (lift σ y).left).trans (val_one _)
    have t₁ : (lift σ y).left ≫ (translT A W.pt⁻¹).left = (lift σ (y * (σ ≫ W.pt)⁻¹)).left := by
      rw [← Over.comp_left, lift_transl, mul_comm, GrpObj.comp_inv]
    have t₂ : (lift σ y).left ≫ (negT A T).left = (lift σ y⁻¹).left := by
      rw [← Over.comp_left, negT, comp_lift, lift_fst, lift_snd_assoc]; rfl
    have e' := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_pull hJ _ _ _).trans (congrArg (val _ · z J) t₁)) rfl)) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_pull hJ _ _ _).trans (congrArg (val _ · z J) t₂)) ((val_inv _ _).trans (congrArg (·⁻¹)
      ((val_pull hJ _ _ _).trans (congrArg (val _ · z J) t₁)))))))).symm.trans e
    let P : LB.Gen (LB.LinComb L.L (fun i => (snd T A).left ≫ φ₁ i) fun i => (k : ℤ) * ε₁ i) :=
      ⟨fun j => (LB.pullGen L.L _ _ ν (snd T A).left).s j ^ k⟩
    have vP : ∀ y : T' ⟶ A, val P (lift σ y).left z J = val ν y.left z J ^ k := fun y =>
      (map_pow _ _ _).trans (congrArg (· ^ k) ((val_pull hJ ν _ _).trans (by rw [← Over.comp_left, lift_snd])))
    have gP : P.IsGen := isGen_of_gm _ fun w j j' h h' => (map_pow _ _ _).trans
      ((congrArg (· ^ k) (gen_trans (pullGen_isGen _ _ _ _ hν _) (𝟙 _) w h h')).trans ((mul_pow _ _ _).trans
        (congrArg₂ (· * ·) (by
          rw [trF, trF, ← Finset.prod_pow]
          exact Finset.prod_congr rfl fun i _ => by rw [mul_comm, zpow_mul, zpow_natCast]) (map_pow _ _ _).symm)))
    have r := fun y => ratio_const hG hA L.isLB (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left])
      (ε := ![(k : ℤ), -(k : ℤ)]) (fun U _ h => by
        have := hF₁ (snd T A) U h
        rw [Fin.prod_univ_two]
        refine (Finset.prod_congr rfl fun i _ => by rw [mul_comm, zpow_mul, zpow_natCast]).trans
          ((Finset.prod_pow _ _ _).trans ?_)
        rw [this, mul_pow, inv_pow]
        show _ = h _ ^ (k : ℤ) * h _ ^ (-(k : ℤ))
        rw [zpow_neg, zpow_natCast, zpow_natCast]; rfl) hmu gP σ y hJ
    have r₁ := congrArg Additive.ofMul (r y)
    have r₂ := congrArg Additive.ofMul (r (y * (σ ≫ W.pt)⁻¹))
    have r₃ := congrArg Additive.ofMul e'
    apply Additive.ofMul.injective
    simp only [vP, ofMul_mul, ofMul_inv, ofMul_one] at r₁ r₂ r₃ ⊢
    linear_combination (norm := abel) r₃ - r₁ + r₂

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
