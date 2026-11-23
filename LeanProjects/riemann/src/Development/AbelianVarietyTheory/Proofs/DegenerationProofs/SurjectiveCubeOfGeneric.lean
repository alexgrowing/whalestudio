import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsValueEq
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsUniqueNormPrim
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalStructureAndSymmetricOfCubeGen
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubTrivDeltaAndEvenUnique

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.EvenTriv

section Alg

variable {A B A₁ U : Type} [CommGroup A] [CommGroup B] [CommGroup A₁] [CommGroup U]

structure Compat (θ : A → A → A → U) (sy : A → U) (a b : B → A) (u : B → U) : Prop where
  cube : ∀ x y v, θ (a x * a y) (a v) (b x * b y * b v) * θ (a x) (a y) (b x * b y * b v) *
      θ (a x) (b x * b y) (b v) * θ (a x) (b x) (b y) * θ (a y) (b x * b y) (b v) * θ (a y) (b x) (b y) *
      θ (a v) (b x * b y) (b v) * θ (a v) (b x) (b y) * u (x * y) * u (x * v) * u (y * v) =
    θ (a x) (a y) (a v) * θ (a x) (a y) (b x * b y) * θ (a x) (b x) (b y) * θ (a y) (b x) (b y) *
      θ (a x) (a v) (b x * b v) * θ (a x) (b x) (b v) * θ (a v) (b x) (b v) *
      θ (a y) (a v) (b y * b v) * θ (a y) (b y) (b v) * θ (a v) (b y) (b v) * u (x * y * v) * u x * u y * u v
  even : ∀ x, u x⁻¹ * sy (a x) * θ (a x)⁻¹ (b x) (b x)⁻¹ = u x * θ (a x) (a x)⁻¹ (b x)

theorem Compat.twist {θ₁ : A₁ → A₁ → A₁ → U} {sy₁ : A₁ → U} {w : A₁ → A₁} {u₁ : A₁ → U}
    (h : Compat θ₁ sy₁ id w u₁) (β : A →* A₁) (a b : B →* A) (hw : ∀ x, w (β (a x)) = β (b x)) (W : A → U)
    {θ : A → A → A → U} {sy : A → U} {u : B → U}
    (hθ : ∀ p q r, θ₁ (β p) (β q) (β r) * W (p * q) * W (p * r) * W (q * r) * W 1 =
      W (p * q * r) * W p * W q * W r * θ p q r)
    (hs : ∀ p, sy₁ (β p) * W p = W p⁻¹ * sy p)
    (hu : ∀ x, u₁ (β (a x)) = W (a x * b x) * W (a x) ^ (-2 : ℤ) * (W (b x))⁻¹ * W 1 ^ (2 : ℤ) * u x) :
    Compat θ sy a b u := by
  have hθ' : ∀ p q r, θ₁ (β p) (β q) (β r) = W (p * q * r) * W p * W q * W r * θ p q r *
      (W (p * q) * W (p * r) * W (q * r) * W 1)⁻¹ := fun p q r =>
    eq_mul_inv_of_mul_eq (by rw [← hθ]; simp only [_root_.mul_assoc])
  have hs' : ∀ p, sy₁ (β p) = W p⁻¹ * sy p * (W p)⁻¹ := fun p => eq_mul_inv_of_mul_eq (hs p)
  constructor
  · intro x y v
    have e := h.cube (β (a x)) (β (a y)) (β (a v))
    simp only [id, hw, ← map_mul β, hθ'] at e
    simp only [← map_mul a, hu] at e
    have e' := congrArg Additive.ofMul e
    apply Additive.ofMul.injective
    simp only [map_mul a, map_mul b] at e'
    generalize a x = p, a y = q, a v = r, b x = p', b y = q', b v = r' at e' ⊢
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ← _root_.mul_assoc] at e' ⊢
    linear_combination (norm := abel) e'
  · intro x
    have e := h.even (β (a x))
    simp only [id, hw, ← map_inv β, hθ', hs'] at e
    simp only [← map_inv a, hu] at e
    have e' := congrArg Additive.ofMul e
    apply Additive.ofMul.injective
    simp only [map_inv a, map_inv b] at e'
    generalize a x = p, b x = p' at e' ⊢
    have n₁ : p⁻¹ * p' * p'⁻¹ = p⁻¹ := mul_inv_cancel_right _ _
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, n₁, mul_inv_cancel, _root_.one_mul, mul_comm p p'] at e' ⊢
    linear_combination (norm := abel) e'

variable {θ : A → A → A → U} {sy : A → U} (a b : B →* A) {u : B → U} {s : B → A → U}

theorem Compat.cub (h : Compat θ sy a b u) (l₁ : ∀ t t' p, s (t * t') p = θ (a t) (a t') p * s t p * s t' p)
    (l₂ : ∀ t p q, s t (p * q) = θ (a t) p q * s t p * s t q) {σ : B → U} (hσ : ∀ x, σ x = s x (b x) * (u x)⁻¹)
    (x y v : B) : σ (x * y * v) * σ x * σ y * σ v = θ (a x) (a y) (a v) * σ (x * y) * σ (x * v) * σ (y * v) := by
  have e' := congrArg Additive.ofMul (h.cube x y v)
  apply Additive.ofMul.injective
  simp only [hσ, l₁]
  simp only [map_mul a, map_mul b, l₂, ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'

theorem Compat.ev (h : Compat θ sy a b u) (l₁ : ∀ t t' p, s (t * t') p = θ (a t) (a t') p * s t p * s t' p)
    (l₂ : ∀ t p q, s t (p * q) = θ (a t) p q * s t p * s t q) (o₁ : ∀ p, s 1 p = 1) (o₂ : ∀ t, s t 1 = 1)
    {σ : B → U} (hσ : ∀ x, σ x = s x (b x) * (u x)⁻¹) (x : B) : σ x⁻¹ = sy (a x) * σ x := by
  have e₀ := congrArg Additive.ofMul (h.even x)
  have e₁ := congrArg Additive.ofMul (l₁ x x⁻¹ (b x))
  have e₂ := congrArg Additive.ofMul (l₂ x⁻¹ (b x) (b x)⁻¹)
  apply Additive.ofMul.injective
  simp only [hσ, mul_inv_cancel, o₁, o₂, map_inv, ofMul_mul, ofMul_inv, ofMul_one] at e₀ e₁ e₂ ⊢
  linear_combination (norm := abel) e₁ - e₂ - e₀

end Alg

open GlobalTheory.PairingLevels

section Rigid

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

def uφ {Y : Over S} (a b : Y ⟶ G) : Fin 4 → (Y.left ⟶ G.left) := ![(a * b).left, a.left, b.left, (1 : Y ⟶ G).left]

def uε : Fin 4 → ℤ := ![1, -2, -1, 2]

theorem prod_u {Y T : Over S} (a b : Y ⟶ G) (x : T ⟶ Y) {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) :
    ∏ k : Fin 4, h (x.left ≫ uφ a b k) ^ uε k =
      h ((x ≫ a) * (x ≫ b)).left * h (x ≫ a).left ^ (-2 : ℤ) * (h (x ≫ b).left)⁻¹ * h (1 : T ⟶ G).left ^ (2 : ℤ) := by
  rw [Fin.prod_univ_four]
  show h (x ≫ (a * b)).left ^ (1 : ℤ) * h (x ≫ a).left ^ (-2 : ℤ) * h (x ≫ b).left ^ (-1 : ℤ) *
    h (x ≫ (1 : Y ⟶ G)).left ^ (2 : ℤ) = _
  rw [MonObj.comp_one, MonObj.comp_mul, zpow_one, zpow_neg_one]

variable {L : LB G.left} {Y : Over S}

omit [GrpObj G] [IsCommMonObj G] in

theorem formEq_of_sum {K K' : Type} [Fintype K] [Fintype K'] {V W : Scheme.{0}} {φ : K → (V ⟶ W)} {ε : K → ℤ}
    {φ' : K' → (V ⟶ W)} {ε' : K' → ℤ}
    (h : ∑ k, ε k • FreeAbelianGroup.of (φ k) = ∑ k, ε' k • FreeAbelianGroup.of (φ' k)) : FormEq φ ε φ' ε' :=
  fun U _ g => by
    have := congrArg (FreeAbelianGroup.lift (fun q => Additive.ofMul (g q))) h
    simp only [map_sum, map_zsmul, FreeAbelianGroup.lift_apply_of] at this
    apply Additive.ofMul.injective
    simpa only [ofMul_prod, ofMul_zpow] using this

omit [GrpObj G] [IsCommMonObj G] in

theorem rep_pull {K : Type} [Fintype K] {V : Over S} {φ : K → (V.left ⟶ G.left)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (p : Y ⟶ V) {D : FreeAbelianGroup (Y.left ⟶ G.left)}
    (hD : ∏ k, Multiplicative.ofAdd (FreeAbelianGroup.of (p.left ≫ φ k)) ^ ε k = Multiplicative.ofAdd D) :
    Rep L D (fun Z r z J => val t (r ≫ p).left z J) := by
  refine ⟨K, inferInstance, _, _, LB.pullGen L φ ε t p.left, DVR.pullGen_isGen _ _ _ _ ht _, ?_,
    fun Z r z J hJ => val_pull hJ _ _ _⟩
  have := congrArg Multiplicative.toAdd hD
  simpa only [toAdd_prod, toAdd_zpow, toAdd_ofAdd] using this

omit [GrpObj G] [IsCommMonObj G] in

theorem rep_unique (hL : L.IsLB) (hp : Function.Surjective Y.hom.appTop.hom) (e : 𝟙_ (Over S) ⟶ Y)
    {D D' : FreeAbelianGroup (Y.left ⟶ G.left)} {f f' : ValFam L Y} (h : Rep L D f) (h' : Rep L D' f') (hD : D = D')
    (he : ∀ z J, Good L z J → f _ e z J = f' _ e z J) {Z : Over S} (r : Z ⟶ Y) {z : Z.left} {J} (hJ : Good L z J) :
    f Z r z J = f' Z r z J := by
  obtain ⟨K, _, φ, ε, t, ht, hs, hv⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', hs', hv'⟩ := h'
  rw [← hv _ _ z J hJ, ← hv' _ _ z J hJ]
  exact gen_unique' hL (formEq_of_sum (hs'.trans (hD.symm.trans hs.symm))) Y.hom e.left (Over.w e) hp ht ht'
    (fun y I hI => (hv _ e y I hI).trans ((he y I hI).trans (hv' _ e y I hI).symm)) _ r.left z J hJ

theorem exists_norm (hL : L.IsLB) (w : G ⟶ G) [IsMonHom w] (H : LBIso L (cubeLB G ![𝟙 G, w] L)) :
    ∃ u : LB.Gen (LB.LinComb L (uφ (𝟙 G) w) uε), u.IsGen ∧
      ∀ (T : Over S) (z : T.left) (J), Good L z J → val u (1 : T ⟶ G).left z J = 1 := by
  obtain ⟨t, ht⟩ := JetSer.exists_gen_of_lbIso L _ _ H
  have R : ∀ p : G ⟶ G, Rep L (pt (p * (p ≫ w)) - pt p - pt (p ≫ w) + pt (1 : G ⟶ G) - pt p)
      (fun Z r z J => val t (r ≫ p).left z J) := fun p => rep_pull ht p (by
    have e : ∀ I : ULift.{0} (Finset (Fin 2)), p.left ≫ (psum G ![𝟙 G, w] I.down).left =
        (psum G ![p, p ≫ w] I.down).left := fun I =>
      congrArg (fun q => q.left) ((psum_hom (preHom p) ![𝟙 G, w] I.down).trans
        (congrArg (fun q => psum G q I.down) (funext fun i => by fin_cases i <;> simp [preHom])))
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, e, Category.comp_id, Fintype.prod_unique]
    rw [JetSer.prod_lam p (p ≫ w) (fun q => Multiplicative.ofAdd (FreeAbelianGroup.of q))]
    simp only [ofAdd_sub, ofAdd_add, div_eq_mul_inv, zpow_neg_one, pt])
  obtain ⟨K, _, φ, ε, t', ht', hs, hv⟩ := (R (𝟙 G)).mul (R 1).inv
  obtain ⟨u, hu, hu'⟩ := exists_gen hL (φ' := uφ (𝟙 G) w) (ε' := uε) (formEq_of_sum (hs.trans (by
    rw [Fin.sum_univ_four, MonObj.one_comp, _root_.mul_one, Category.id_comp]
    show _ = (1 : ℤ) • pt (𝟙 G * w) + (-2 : ℤ) • pt (𝟙 G) + (-1 : ℤ) • pt w + (2 : ℤ) • pt (1 : G ⟶ G)
    abel))) t' ht'
  refine ⟨u, hu, fun T z J hJ => ?_⟩
  rw [hu' _ _ z J hJ, hv T 1 z J hJ]
  simp only [Category.comp_id, MonObj.comp_one, mul_inv_cancel]

theorem compat_of_surjective (h3 : Function.Surjective (G3 G).hom.appTop.hom) (P : CP G) (w : G ⟶ G) [IsMonHom w]
    {u : LB.Gen (LB.LinComb P.L.L (uφ (𝟙 G) w) uε)} (hu : u.IsGen)
    (h1 : ∀ (T : Over S) (z : T.left) (J), Good P.L.L z J → val u (1 : T ⟶ G).left z J = 1)
    (T : Over S) (z : T.left) (J) (hJ : Good P.L.L z J) :
    Compat (cubV P.c z J) (fun x : T ⟶ G => val P.sym x.left z J) id (· ≫ w) (fun x => val u x.left z J) := by
  have C : ∀ a b d : G3 G ⟶ G, Rep P.L.L
      (pt (a * b * d) - pt (a * b) - pt (a * d) - pt (b * d) + pt a + pt b + pt d - pt (1 : G3 G ⟶ G))
      (fun Z r z J => cubV P.c z J (r ≫ a) (r ≫ b) (r ≫ d)) := fun a b d => Rep.cube P.c.isGen a b d
  have Ru : ∀ p : G3 G ⟶ G, Rep P.L.L (pt (p * (p ≫ w)) - (2 : ℤ) • pt p - pt (p ≫ w) + (2 : ℤ) • pt (1 : G3 G ⟶ G))
      (fun Z r z J => val u (r ≫ p).left z J) := fun p => rep_pull hu p (by
    rw [prod_u (𝟙 G) w p (fun q => Multiplicative.ofAdd (FreeAbelianGroup.of q))]
    simp only [ofAdd_sub, ofAdd_add, div_eq_mul_inv, zpow_neg, ofAdd_zsmul, pt, Category.comp_id])
  have Rs : ∀ p : G3 G ⟶ G, Rep P.L.L (pt p⁻¹ - pt p) (fun Z r z J => val P.sym (r ≫ p).left z J) := fun p =>
    rep_pull P.sym_gen p (by
      rw [prod_sym p (fun q => Multiplicative.ofAdd (FreeAbelianGroup.of q))]
      simp only [ofAdd_sub, div_eq_mul_inv, pt])
  obtain ⟨a, ha⟩ : ∃ a, a = x3 G 0 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = x3 G 1 := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = x3 G 2 := ⟨_, rfl⟩
  have r₀ : ∀ {Z : Over S} (x y v : Z ⟶ G), lift x (lift y v) ≫ a = x := fun x y v => by simp [ha, x3]
  have r₁ : ∀ {Z : Over S} (x y v : Z ⟶ G), lift x (lift y v) ≫ b = y := fun x y v => by simp [hb, x3]
  have r₂ : ∀ {Z : Over S} (x y v : Z ⟶ G), lift x (lift y v) ≫ d = v := fun x y v => by simp [hd, x3]
  constructor
  · intro x y v
    have e := rep_unique P.L.isLB h3 (lift 1 (lift 1 1))
      (((((((((((C (a * b) d ((a ≫ w) * (b ≫ w) * (d ≫ w))).mul (C a b ((a ≫ w) * (b ≫ w) * (d ≫ w)))).mul
        (C a ((a ≫ w) * (b ≫ w)) (d ≫ w))).mul (C a (a ≫ w) (b ≫ w))).mul
        (C b ((a ≫ w) * (b ≫ w)) (d ≫ w))).mul (C b (a ≫ w) (b ≫ w))).mul
        (C d ((a ≫ w) * (b ≫ w)) (d ≫ w))).mul (C d (a ≫ w) (b ≫ w))).mul (Ru (a * b))).mul (Ru (a * d))).mul
        (Ru (b * d)))
      ((((((((((((((C a b d).mul (C a b ((a ≫ w) * (b ≫ w)))).mul (C a (a ≫ w) (b ≫ w))).mul
        (C b (a ≫ w) (b ≫ w))).mul (C a d ((a ≫ w) * (d ≫ w)))).mul (C a (a ≫ w) (d ≫ w))).mul
        (C d (a ≫ w) (d ≫ w))).mul (C b d ((b ≫ w) * (d ≫ w)))).mul (C b (b ≫ w) (d ≫ w))).mul
        (C d (b ≫ w) (d ≫ w))).mul (Ru (a * b * d))).mul (Ru a)).mul (Ru b)).mul (Ru d))
      (by simp only [MonObj.mul_comp, ← _root_.mul_assoc]; abel)
      (fun y I hI => by
        simp only [MonObj.comp_mul, ← Category.assoc, r₀, r₁, r₂, MonObj.one_comp, _root_.mul_one,
          (isCub_cubV P.c hI).face, h1 _ y I hI]) (lift x (lift y v)) hJ
    simpa only [MonObj.comp_mul, ← Category.assoc, r₀, r₁, r₂, id] using e
  · intro x
    have e := rep_unique P.L.isLB h3 (lift 1 (lift 1 1))
      (((Ru a⁻¹).mul (Rs a)).mul (C a⁻¹ (a ≫ w) (a ≫ w)⁻¹)) ((Ru a).mul (C a a⁻¹ (a ≫ w)))
      (by
        simp only [GrpObj.inv_comp, mul_inv_cancel_right, mul_inv_cancel, _root_.one_mul]; abel)
      (fun y I hI => by
        simp only [GrpObj.comp_inv, ← Category.assoc, r₀, MonObj.one_comp, _root_.mul_one, inv_one,
          (isCub_cubV P.c hI).face, h1 _ y I hI, P.val_sym_one hI]) (lift x (lift 1 1)) hJ
    simpa only [GrpObj.comp_inv, ← Category.assoc, r₀, id] using e

end Rigid

section Transfer

variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]

def postHom (i : H ⟶ G) [IsMonHom i] (T : Over S) : (T ⟶ H) →* (T ⟶ G) :=
  MonoidHom.mk' (· ≫ i) fun _ _ => MonObj.mul_comp _ _ _

theorem exists_even_of_compat (P : CP G) (i j : H ⟶ G) [IsMonHom i]
    (hj : ∀ (T : Over S) (x y : T ⟶ H), (x * y) ≫ j = (x ≫ j) * (y ≫ j))
    {u : LB.Gen (LB.LinComb P.L.L (uφ i j) uε)} (hu : u.IsGen)
    (hc : ∀ (T : Over S) (z : T.left) (J), Good P.L.L z J → Compat (cubV P.c z J) (fun x : T ⟶ G => val P.sym x.left z J)
      (fun x : T ⟶ H => x ≫ i) (· ≫ j) (fun x => val u x.left z J))
    (s : BiTriv P.c i) : ∃ σ : CubTriv P.c i, σ.Even := by
  obtain ⟨t, ht, hv⟩ := exists_gen P.L.isLB (φ' := ![i.left, (1 : H ⟶ G).left]) (ε' := ![1, -1]) (fun V _ k => by
      have e₁ := CubTrivTorus.prod_cubTriv i (𝟙 H) k
      have e₂ := prod_u i j (𝟙 H) k
      simp only [Over.id_left, Category.id_comp] at e₁ e₂
      refine (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := V) _ (CubTrivTorus.prod_biTriv i (𝟙 H) j k)
        (DVR.prod_neg _ _ e₂)).trans (Eq.trans ?_ e₁.symm)
      apply Additive.ofMul.injective
      simp only [Category.id_comp, ofMul_mul, ofMul_inv, ofMul_zpow]
      abel)
    (LB.mulGen P.L.L _ _ _ _ (LB.pullGen P.L.L _ _ s.s (lift (𝟙 H) j).left) (LB.invGen P.L.L _ _ u))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ s.gen _) (DVR.invGen_isGen _ _ _ _ hu))
  have hσ : ∀ (T : Over S) (z : T.left) (J), Good P.L.L z J → ∀ x : T ⟶ H,
      val t x.left z J = val s.s (lift x (x ≫ j)).left z J * (val u x.left z J)⁻¹ := fun T z J hJ x => by
    refine (hv _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_pull hJ _ _ _).trans ?_)
      (val_inv _ _)))
    rw [← Over.comp_left, comp_lift, Category.comp_id]
  refine ⟨⟨t, ht, fun T x y v z J hJ => ?_⟩, fun T x z J hJ => ?_⟩
  · exact Compat.cub (postHom i T) (MonoidHom.mk' (· ≫ j) (hj T)) (s := fun a p => val s.s (lift a p).left z J)
      (hc T z J hJ) (fun a a' p => s.law1 T a a' p z J hJ) (fun a p q => s.law2 T a p q z J hJ)
      (σ := fun a => val t a.left z J) (hσ T z J hJ) x y v
  · exact Compat.ev (postHom i T) (MonoidHom.mk' (· ≫ j) (hj T)) (s := fun a p => val s.s (lift a p).left z J)
      (hc T z J hJ) (fun a a' p => s.law1 T a a' p z J hJ) (fun a p q => s.law2 T a p q z J hJ)
      (s.val_one_left hJ) (s.val_one_right hJ) (σ := fun a => val t a.left z J) (hσ T z J hJ) x

theorem exists_even_of_surjective {S₁ : Scheme.{0}} {G₁ : Over S₁} [GrpObj G₁] [IsCommMonObj G₁]
    (h3 : Function.Surjective (G3 G₁).hom.appTop.hom) (P₁ : CP G₁) (w : G₁ ⟶ G₁) [IsMonHom w]
    (hw : LBIso P₁.L.L (cubeLB G₁ ![𝟙 G₁, w] P₁.L.L)) (P : CP G) {f : S ⟶ S₁} {F : G.left ⟶ G₁.left}
    (h : IsPullback F G.hom G₁.hom f) {v : LB.Iso P.L.L (P₁.L.L.pull F)} (hv : IsCPMap P P₁ f F h.w v)
    (i : H ⟶ G) [IsMonHom i] (s : BiTriv P.c i) : ∃ σ : CubTriv P.c i, σ.Even := by
  obtain ⟨u₁, hu₁, h1⟩ := exists_norm P₁.L.isLB w hw
  let j : H ⟶ G := Over.homMk (h.lift (i.left ≫ F ≫ w.left) H.hom (by
    rw [Category.assoc, Category.assoc, Over.w, h.w, ← Category.assoc, Over.w])) (h.lift_snd _ _ _)
  have hjF : j.left ≫ F = i.left ≫ F ≫ w.left := h.lift_fst _ _ _
  let β := toBaseHom hv.mul
  have hβ : ∀ (T : Over S) (x : T ⟶ H), β T (x ≫ i) ≫ w = β T (x ≫ j) := fun T x => Over.OverMorphism.ext (by
    show ((x.left ≫ i.left) ≫ F) ≫ w.left = (x.left ≫ j.left) ≫ F
    simp only [Category.assoc, hjF])
  have hj : ∀ (T : Over S) (x y : T ⟶ H), (x * y) ≫ j = (x ≫ j) * (y ≫ j) := fun T x y => by
    have e : β T ((x * y) ≫ j) = β T ((x ≫ j) * (y ≫ j)) := by
      rw [map_mul, ← hβ, ← hβ, ← hβ, MonObj.mul_comp, map_mul, MonObj.mul_comp]
    exact Over.OverMorphism.ext (h.hom_ext (congrArg (fun q => q.left) e) ((Over.w _).trans (Over.w _).symm))
  have hc : ∀ k, uφ i j k ≫ F = (i.left ≫ F) ≫ uφ (𝟙 G₁) w k := fun k => by
    have e := hβ H (𝟙 H)
    rw [Category.id_comp, Category.id_comp] at e
    fin_cases k
    · show (β H (i * j)).left = (β H i ≫ (𝟙 G₁ * w)).left
      rw [map_mul, MonObj.comp_mul, Category.comp_id, e]
    · exact (Category.comp_id _).symm
    · exact hjF.trans (Category.assoc _ _ _).symm
    · show (β H 1).left = (β H i ≫ (1 : G₁ ⟶ G₁)).left
      rw [map_one, MonObj.comp_one]
  obtain ⟨u, hu, Hu⟩ := CubTransport.exists_pmaps ((isGen_iff v).1 hv.gen) P₁.L.isLB P.L.isLB (i.left ≫ F) hc u₁ hu₁
  refine exists_even_of_compat P i j hj hu (fun T z J hJ => ?_) s
  obtain ⟨J₁, hJ₁⟩ := exists_good_pt P₁.L.isLB z
  obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ,
    ∀ x, W x = gw v x.left z (J₁ (x.left ≫ F)) (J x.left) := ⟨_, fun _ => rfl⟩
  obtain ⟨-, a₂, a₃⟩ := hv.vals T z J J₁ hJ hJ₁ W hW
  refine (compat_of_surjective h3 P₁ w hu₁ h1 (Over.mk (T.hom ≫ f)) z J₁ hJ₁).twist (β T) (postHom i T)
    (MonoidHom.mk' (· ≫ j) (hj T)) (hβ T) W a₃ a₂ fun x => ?_
  have e := (CubTransport.val_pmaps hc Hu x.left hJ₁ hJ).trans
    (congrArg₂ (· * ·) (prod_u i j x (fun q => gw v q z (J₁ (q ≫ F)) (J q))) rfl)
  simp only [← hW] at e
  rw [← Category.assoc] at e
  exact e

end Transfer

theorem surjective_cube_of_generic {R : Type} [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    (hG : IsSemiAbelian G) (hp : IsProper (pullback.snd G.hom (jK R))) :
    Function.Surjective (G3 G).hom.appTop.hom := by
  have hab : genericPoints (Spec (CommRingCat.of R)) ⊆ abLocus G := by
    have : IsProper ((Over.pullback (jK R)).obj G).hom := hp
    refine Set.Subset.trans ?_ (range_subset_abLocus_of_isProper (G' := (Over.pullback (jK R)).obj G) hG
      (IsPullback.of_hasPullback G.hom (jK R)))
    rw [genericPoints_eq_singleton, genericPoint_eq_bot_of_affine]
    rintro _ rfl
    refine ⟨(⊥ : PrimeSpectrum (FractionRing R)), PrimeSpectrum.ext ?_⟩
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))
  have a₁ := hG.smooth
  have := hG.geomConnected
  have b₁ := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ G
  obtain ⟨a₂, b₂, c₂⟩ := GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj _ G G a₁ a₁ b₁ b₁
  obtain ⟨a₃, b₃, c₃⟩ := GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj _ G _ a₁ a₂ b₁ b₂
  exact CubeGen.surjective_appTop _ (lift 1 (lift 1 1)) a₃ b₃ inferInstance
    ((Set.subset_inter hab ((Set.subset_inter hab hab).trans c₂)).trans c₃)

theorem exists_even_cubTriv : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (G₁ : Over (Spec (CommRingCat.of R))) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → IsProper (pullback.snd G₁.hom (jK R)) → ∀ (P₁ : CP G₁) (w : G₁ ⟶ G₁), IsMonHom w → LBIso P₁.L.L (cubeLB G₁ ![𝟙 G₁, w] P₁.L.L) → ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (X : Type) [AddCommGroup X] (Q : TQ G X) (P : CP G) (f : S ⟶ Spec (CommRingCat.of R)) (F : G.left ⟶ G₁.left) (h : IsPullback F G.hom G₁.hom f) (v : LB.Iso P.L.L (P₁.L.L.pull F)), IsCPMap P P₁ f F h.w v → Nonempty (BiTriv P.c Q.i) → ∃ σ : CubTriv P.c Q.i, σ.Even := by
  intro _ _ R _ _ G₁ _ _ hG hp P₁ w _ hw S G _ _ X _ Q P f F h v hv ⟨s⟩
  have := Q.i_hom
  exact exists_even_of_surjective (surjective_cube_of_generic G₁ hG hp) P₁ w hw P h hv Q.i s

end GlobalTheory.EvenTriv
