import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

def tup {T : Over S} (x x' y : T ⟶ A) : T ⟶ powObj A 3 := lift x (lift x' (lift y (toUnit T)))

omit [GrpObj A] in
theorem tup_0 {T : Over S} (x x' y : T ⟶ A) : tup x x' y ≫ powPr A (0 : Fin 3) = x := lift_fst _ _

omit [GrpObj A] in
theorem tup_1 {T : Over S} (x x' y : T ⟶ A) : tup x x' y ≫ powPr A (1 : Fin 3) = x' :=
  (lift_snd_assoc _ _ _).trans (lift_fst _ _)

omit [GrpObj A] in
theorem tup_2 {T : Over S} (x x' y : T ⟶ A) : tup x x' y ≫ powPr A (2 : Fin 3) = y :=
  (lift_snd_assoc _ _ _).trans ((lift_snd_assoc _ _ _).trans (lift_fst _ _))

theorem ratio_pow (hp : Function.Surjective (powObj A 3).hom.appTop.hom) {M : LB A.left} (hM : M.IsLB) {K K' : Type}
    [Fintype K] [Fintype K'] {φ : K → ((powObj A 3).left ⟶ A.left)} {ε : K → ℤ} {φ' : K' → ((powObj A 3).left ⟶ A.left)}
    {ε' : K' → ℤ} (hF : FormEq φ' ε' φ ε) {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen)
    (hu' : u'.IsGen) {T : Over S} (x x' y : T ⟶ A) {z : T.left} {J} (hJ : Good M z J) :
    val u (tup x x' y).left z J * val u' (tup (1 : T ⟶ A) 1 1).left z J =
      val u' (tup x x' y).left z J * val u (tup (1 : T ⟶ A) 1 1).left z J := by
  let n : powObj A 3 ⟶ powObj A 3 := tup 1 1 1
  have hn : ∀ {T : Over S} (ρ : T ⟶ powObj A 3), ρ.left ≫ n.left = (tup (1 : T ⟶ A) 1 1).left := fun {T} ρ =>
    congrArg (fun q : T ⟶ powObj A 3 => q.left) ((comp_lift _ _ _).trans (congrArg₂ lift (MonObj.comp_one _)
      ((comp_lift _ _ _).trans (congrArg₂ lift (MonObj.comp_one _) ((comp_lift _ _ _).trans
        (congrArg₂ lift (MonObj.comp_one _) (toUnit_unique _ _)))))))
  have key := gen_unique' hM (fun U _ h => (prod_sum₂ (K := K') (K' := K) (U := U) _ (hF U h)
      (c' := ∏ k, h (n.left ≫ φ k) ^ ε k) rfl).trans (prod_sum₂ (K := K) (K' := K') (U := U) _ rfl
      (hF U fun q => h (n.left ≫ q))).symm) (powObj A 3).hom (tup (1 : 𝟙_ (Over S) ⟶ A) 1 1).left (Over.w _) hp
    (mulGen_isGen _ _ _ _ _ _ _ hu (pullGen_isGen _ _ _ _ hu' n.left))
    (mulGen_isGen _ _ _ _ _ _ _ hu' (pullGen_isGen _ _ _ _ hu n.left)) (fun w I hI => by
      have e := hn (tup (1 : 𝟙_ (Over S) ⟶ A) 1 1)
      exact ((val_mul hI _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hI _ _ _).trans (congrArg (val u' · w I) e)))).trans
        ((mul_comm _ _).trans ((val_mul hI _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hI _ _ _).trans
          (congrArg (val u · w I) e)))).symm)) _ (tup x x' y).left z J hJ
  rwa [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, hn] at key

section

variable [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L) {T T' : Over S}

def cubε : thK.{0} → ℤ := thε

def cubφ (x x' y : T ⟶ A) : thK.{0} → (T.left ⟶ A.left) := fun I => (lift x (lift x' y)).left ≫ thφ A (x3 A) I

def cubG (x x' y : T ⟶ A) : LB.Gen (LB.LinComb L.L (cubφ x x' y) cubε) :=
  LB.pullGen L.L (thφ A (x3 A)) thε c.t (lift x (lift x' y)).left

theorem prod_cubφ (x x' y : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ A.left) → U) :
    ∏ I, h (cubφ x x' y I) ^ cubε I = h (x * x' * y).left * (h (x * x').left)⁻¹ * (h (x * y).left)⁻¹ * (h (x' * y).left)⁻¹ *
      h x.left * h x'.left * h y.left * (h (1 : T ⟶ A).left)⁻¹ := prod_cub x x' y h

theorem cubG_isGen (x x' y : T ⟶ A) : (cubG c x x' y).IsGen := pullGen_isGen _ _ _ _ c.isGen _

theorem val_cubG (ρ : T' ⟶ T) {z : T'.left} {J} (hJ : Good L.L z J) (x x' y : T ⟶ A) :
    val (cubG c x x' y) ρ.left z J = cubV c z J (ρ ≫ x) (ρ ≫ x') (ρ ≫ y) := val_cub c ρ hJ x x' y

attribute [irreducible] cubG cubφ cubε

end

variable [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L) (hp : Function.Surjective (powObj A 3).hom.appTop.hom)
  {O : Type} [CommRing O] [StarRing O] (o : OAct O A) {K : Type} [Fintype K] {φ : O → K → ((A ⊗ A).left ⟶ A.left)} {ε : K → ℤ}
  (w : ∀ a, LB.Gen (LB.LinComb L.L (φ a) ε)) (hw : ∀ a, (w a).IsGen)
  (hW : ∀ a {T : Over S} (x y : T ⟶ A) (U : Type) [CommGroup U] (h : (T.left ⟶ A.left) → U),
    ∏ i, h ((lift x y).left ≫ φ a i) ^ ε i = h (x * (y ≫ o.act (star a))).left * (h x.left)⁻¹ *
      (h (y ≫ o.act (star a)).left)⁻¹ * ((h ((x ≫ o.act a) * y).left)⁻¹ * h (x ≫ o.act a).left * h y.left))
  {T : Over S} {z : T.left} {J : (T.left ⟶ A.left) → L.L.ι} (hJ : Good L.L z J)
  (h1 : ∀ a, val₂ (w a) z J (1 : T ⟶ A) 1 = 1)
include c hp hw hW hJ h1

theorem cubical_law_left (a : O) (x x' y : T ⟶ A) :
    val₂ (w a) z J (x * x') y * cubV c z J (x ≫ o.act a) (x' ≫ o.act a) y =
      val₂ (w a) z J x y * val₂ (w a) z J x' y * cubV c z J x x' (y ≫ o.act (star a)) := by
  have := fun a => o.hom a
  have C : IsCub (cubV c z J) := isCub_cubV c hJ
  have key := ratio_pow hp L.isLB (fun U _ h => (prod_sum₂ (K := (K ⊕ K)) (K' := thK.{0}) (U := U) _ (prod_sum₂ (K := K) (K' := K) (U := U) _ (hW a (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3)) U h) (hW a (powPr A (1 : Fin 3)) (powPr A (2 : Fin 3)) U h)) (prod_cubφ (powPr A (0 : Fin 3)) (powPr A (1 : Fin 3)) ((powPr A (2 : Fin 3)) ≫ o.act (star a)) h)).trans (Eq.trans (by
      simp only [MonObj.mul_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) (prod_sum₂ (K := K) (K' := thK.{0}) (U := U) _ (hW a ((powPr A (0 : Fin 3)) * (powPr A (1 : Fin 3))) (powPr A (2 : Fin 3)) U h) (prod_cubφ ((powPr A (0 : Fin 3)) ≫ o.act a) ((powPr A (1 : Fin 3)) ≫ o.act a) (powPr A (2 : Fin 3)) h)).symm))
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ (hw a) (lift ((powPr A (0 : Fin 3)) * (powPr A (1 : Fin 3))) (powPr A (2 : Fin 3))).left) (cubG_isGen c ((powPr A (0 : Fin 3)) ≫ o.act a) ((powPr A (1 : Fin 3)) ≫ o.act a) (powPr A (2 : Fin 3))))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ (hw a) (lift (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3))).left) (pullGen_isGen _ _ _ _ (hw a) (lift (powPr A (1 : Fin 3)) (powPr A (2 : Fin 3))).left)) (cubG_isGen c (powPr A (0 : Fin 3)) (powPr A (1 : Fin 3)) ((powPr A (2 : Fin 3)) ≫ o.act (star a)))) x x' y hJ
  simp only [val_mul hJ, val_ros _ _ hJ, val_cubG c _ hJ, MonObj.comp_mul, ← Category.assoc, tup_0, tup_1, tup_2,
    MonObj.one_comp, _root_.mul_one, h1, C.face] at key
  exact key

theorem cubical_law_right (a : O) (x x' y : T ⟶ A) :
    val₂ (w a) z J x (x' * y) * cubV c z J (x ≫ o.act a) x' y =
      val₂ (w a) z J x x' * val₂ (w a) z J x y * cubV c z J x (x' ≫ o.act (star a)) (y ≫ o.act (star a)) := by
  have := fun a => o.hom a
  have C : IsCub (cubV c z J) := isCub_cubV c hJ
  have key := ratio_pow hp L.isLB (fun U _ h => (prod_sum₂ (K := (K ⊕ K)) (K' := thK.{0}) (U := U) _ (prod_sum₂ (K := K) (K' := K) (U := U) _ (hW a (powPr A (0 : Fin 3)) (powPr A (1 : Fin 3)) U h) (hW a (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3)) U h)) (prod_cubφ (powPr A (0 : Fin 3)) ((powPr A (1 : Fin 3)) ≫ o.act (star a)) ((powPr A (2 : Fin 3)) ≫ o.act (star a)) h)).trans (Eq.trans (by
      simp only [MonObj.mul_comp, _root_.mul_assoc]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) (prod_sum₂ (K := K) (K' := thK.{0}) (U := U) _ (hW a (powPr A (0 : Fin 3)) ((powPr A (1 : Fin 3)) * (powPr A (2 : Fin 3))) U h) (prod_cubφ ((powPr A (0 : Fin 3)) ≫ o.act a) (powPr A (1 : Fin 3)) (powPr A (2 : Fin 3)) h)).symm))
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ (hw a) (lift (powPr A (0 : Fin 3)) ((powPr A (1 : Fin 3)) * (powPr A (2 : Fin 3)))).left) (cubG_isGen c ((powPr A (0 : Fin 3)) ≫ o.act a) (powPr A (1 : Fin 3)) (powPr A (2 : Fin 3))))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ (hw a) (lift (powPr A (0 : Fin 3)) (powPr A (1 : Fin 3))).left) (pullGen_isGen _ _ _ _ (hw a) (lift (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3))).left)) (cubG_isGen c (powPr A (0 : Fin 3)) ((powPr A (1 : Fin 3)) ≫ o.act (star a)) ((powPr A (2 : Fin 3)) ≫ o.act (star a)))) x x' y hJ
  simp only [val_mul hJ, val_ros _ _ hJ, val_cubG c _ hJ, MonObj.comp_mul, ← Category.assoc, tup_0, tup_1, tup_2,
    MonObj.one_comp, _root_.mul_one, h1, C.face] at key
  exact key

theorem adv_mul (a b : O) (x x' y : T ⟶ A) :
    val₂ (w (a * b)) z J x y = val₂ (w a) z J (x ≫ o.act b) y * val₂ (w b) z J x (y ≫ o.act (star a)) := by
  have := fun a => o.hom a
  have C : IsCub (cubV c z J) := isCub_cubV c hJ
  have key := ratio_pow hp L.isLB (fun U _ h => (prod_sum₂ (K := K) (K' := K) (U := U) _ (hW a ((powPr A (0 : Fin 3)) ≫ o.act b) (powPr A (2 : Fin 3)) U h) (hW b (powPr A (0 : Fin 3)) ((powPr A (2 : Fin 3)) ≫ o.act (star a)) U h)).trans (Eq.trans (by
      simp only [star_mul, mul_comm (star b), mul_comm a b, o.mul, Category.assoc]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) (hW (a * b) (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3)) U h).symm))
    (pullGen_isGen _ _ _ _ (hw (a * b)) (lift (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3))).left)
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ (hw a) (lift ((powPr A (0 : Fin 3)) ≫ o.act b) (powPr A (2 : Fin 3))).left) (pullGen_isGen _ _ _ _ (hw b) (lift (powPr A (0 : Fin 3)) ((powPr A (2 : Fin 3)) ≫ o.act (star a))).left)) x x' y hJ
  simp only [val_mul hJ, val_ros _ _ hJ, val_cubG c _ hJ, MonObj.comp_mul, ← Category.assoc, tup_0, tup_1, tup_2,
    MonObj.one_comp, _root_.mul_one, h1, C.face] at key
  exact key

theorem adv_add (a b : O) (x x' y : T ⟶ A) :
    val₂ (w (a + b)) z J x y * cubV c z J (x ≫ o.act a) (x ≫ o.act b) y =
      val₂ (w a) z J x y * val₂ (w b) z J x y * cubV c z J x (y ≫ o.act (star a)) (y ≫ o.act (star b)) := by
  have := fun a => o.hom a
  have C : IsCub (cubV c z J) := isCub_cubV c hJ
  have key := ratio_pow hp L.isLB (fun U _ h => (prod_sum₂ (K := (K ⊕ K)) (K' := thK.{0}) (U := U) _ (prod_sum₂ (K := K) (K' := K) (U := U) _ (hW a (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3)) U h) (hW b (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3)) U h)) (prod_cubφ (powPr A (0 : Fin 3)) ((powPr A (2 : Fin 3)) ≫ o.act (star a)) ((powPr A (2 : Fin 3)) ≫ o.act (star b)) h)).trans (Eq.trans (by
      simp only [star_add, o.add, MonObj.comp_mul, _root_.mul_assoc]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) (prod_sum₂ (K := K) (K' := thK.{0}) (U := U) _ (hW (a + b) (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3)) U h) (prod_cubφ ((powPr A (0 : Fin 3)) ≫ o.act a) ((powPr A (0 : Fin 3)) ≫ o.act b) (powPr A (2 : Fin 3)) h)).symm))
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ (hw (a + b)) (lift (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3))).left) (cubG_isGen c ((powPr A (0 : Fin 3)) ≫ o.act a) ((powPr A (0 : Fin 3)) ≫ o.act b) (powPr A (2 : Fin 3))))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ (hw a) (lift (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3))).left) (pullGen_isGen _ _ _ _ (hw b) (lift (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3))).left)) (cubG_isGen c (powPr A (0 : Fin 3)) ((powPr A (2 : Fin 3)) ≫ o.act (star a)) ((powPr A (2 : Fin 3)) ≫ o.act (star b)))) x x' y hJ
  simp only [val_mul hJ, val_ros _ _ hJ, val_cubG c _ hJ, MonObj.comp_mul, ← Category.assoc, tup_0, tup_1, tup_2,
    MonObj.one_comp, _root_.mul_one, h1, C.face] at key
  exact key

theorem adv_sy (a : O) (x x' y : T ⟶ A) :
    val₂ (w a) z J x y * val₂ (w (star a)) z J y x * val₂ (w 1) z J x y = val₂ (w 1) z J x y := by
  have := fun a => o.hom a
  have C : IsCub (cubV c z J) := isCub_cubV c hJ
  have key := ratio_pow hp L.isLB (fun U _ h => (hW 1 (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3)) U h).trans (Eq.trans (by
      simp only [star_star, mul_comm (powPr A (2 : Fin 3)), mul_comm ((powPr A (2 : Fin 3)) ≫ o.act (star a))]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) (prod_sum₂ (K := (K ⊕ K)) (K' := K) (U := U) _ (prod_sum₂ (K := K) (K' := K) (U := U) _ (hW a (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3)) U h) (hW (star a) (powPr A (2 : Fin 3)) (powPr A (0 : Fin 3)) U h)) (hW 1 (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3)) U h)).symm))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ (hw a) (lift (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3))).left) (pullGen_isGen _ _ _ _ (hw (star a)) (lift (powPr A (2 : Fin 3)) (powPr A (0 : Fin 3))).left)) (pullGen_isGen _ _ _ _ (hw 1) (lift (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3))).left))
    (pullGen_isGen _ _ _ _ (hw 1) (lift (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3))).left) x x' y hJ
  simp only [val_mul hJ, val_ros _ _ hJ, val_cubG c _ hJ, MonObj.comp_mul, ← Category.assoc, tup_0, tup_1, tup_2,
    MonObj.one_comp, _root_.mul_one, h1, C.face] at key
  exact key

theorem adv_one (x y : T ⟶ A) : val₂ (w 1) z J x y = 1 := by
  have := adv_mul c hp o w hw hW hJ h1 1 1 x x y
  rw [_root_.mul_one, star_one, o.one, Category.comp_id, Category.comp_id] at this
  exact mul_eq_left.1 this.symm

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
