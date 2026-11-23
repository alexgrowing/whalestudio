import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RosatiCube

open ReciprocityTheory.ChartRestriction.G.DVR

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

def IsNormGen (L : LB A.left) (f g : A ⟶ A) (u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)) : Prop :=
  u.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L)

variable {L : LB A.left}

theorem IsNormGen.val_origin {f g : A ⟶ A} {u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)} (hu : IsNormGen L f g u)
    {y : (𝟙_ (Over S)).left} {J} (hJ : Good L y J) : val₂ u y J (1 : 𝟙_ (Over S) ⟶ A) 1 = 1 := by
  have e : lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A) = lift η[A] η[A] := by simp [Hom.one_def]
  have := val_corr hJ hu.2 (𝟙 _)
  rw [val_pull hJ, Category.id_comp, val_one] at this
  rw [val₂, e]; exact this

omit [IsCommMonObj A] in
theorem val_pull_pair {K : Type} [Fintype K] {φ : K → ((A ⊗ A).left ⟶ A.left)} {ε : K → ℤ}
    (u : LB.Gen (LB.LinComb L φ ε)) {T T' : Over S} (ρ : T' ⟶ T) {z : T'.left} {J} (hJ : Good L z J) (a b : T ⟶ A) :
    val (LB.pullGen L _ _ u (lift a b).left) ρ.left z J = val₂ u z J (ρ ≫ a) (ρ ≫ b) := by
  rw [val_pull hJ, ← Over.comp_left, comp_lift]; rfl

theorem pair_unique_of_surj (sj : Function.Surjective (A ⊗ A).hom.appTop.hom) (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → ((A ⊗ A).left ⟶ A.left)} {ε : K → ℤ} {φ' : K' → ((A ⊗ A).left ⟶ A.left)} {ε' : K' → ℤ}
    (hF : FormEq φ' ε' φ ε) {u : LB.Gen (LB.LinComb L φ ε)} {u' : LB.Gen (LB.LinComb L φ' ε')} (hu : u.IsGen)
    (hu' : u'.IsGen) (h : ∀ y J, Good L y J → val u (lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A)).left y J =
      val u' (lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A)).left y J)
    {Z : Scheme.{0}} (r : Z ⟶ (A ⊗ A).left) {z : Z} {J} (hJ : Good L z J) : val u r z J = val u' r z J :=
  gen_unique' hL hF (A ⊗ A).hom _
    (Over.w (lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A)))
    sj hu hu' h Z r z J hJ

variable {Lr : RigLB A} (c : CubicalStr A Lr)

theorem ros_add_of_surj (sj : Function.Surjective (A ⊗ A ⊗ A).hom.appTop.hom) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε)) (hu : u.IsGen)
    (h₀ : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (zero2 A)) (LB.oneGen Lr.L)) {T : Over S} {z : T.left} {J}
    (hJ : Good Lr.L z J) (x x' y : T ⟶ A) :
    val₂ u z J (x * x') y * cubV c z J x x' (y ≫ g) =
        cubV c z J (x ≫ f) (x' ≫ f) y * (val₂ u z J x y * val₂ u z J x' y) ∧
      val₂ u z J y (x * x') * cubV c z J y (x ≫ g) (x' ≫ g) =
        cubV c z J (y ≫ f) x x' * (val₂ u z J y x * val₂ u z J y x') := by
  let p₀ := x3 A 0
  let p₁ := x3 A 1
  let p₂ := x3 A 2
  have mf : ∀ {T : Over S} (a b : T ⟶ A), (a * b) ≫ f = (a ≫ f) * (b ≫ f) := fun a b => MonObj.mul_comp a b f
  have mg : ∀ {T : Over S} (a b : T ⟶ A), (a * b) ≫ g = (a ≫ g) * (b ≫ g) := fun a b => MonObj.mul_comp a b g
  have vp : ∀ {T T' : Over S} (ρ : T' ⟶ T) {z : T'.left} {J}, Good Lr.L z J → ∀ a b : T ⟶ A,
      val (LB.pullGen Lr.L _ _ u (lift a b).left) ρ.left z J = val₂ u z J (ρ ≫ a) (ρ ≫ b) := fun ρ z J hJ a b => by
    rw [val_pull hJ, ← Over.comp_left, comp_lift]; rfl
  have v1 : ∀ {y : (𝟙_ (Over S)).left} {J}, Good Lr.L y J → val₂ u y J (1 : 𝟙_ (Over S) ⟶ A) 1 = 1 := fun {y J} hJ => by
    have e : lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A) = lift η[A] η[A] := by simp [Hom.one_def]
    have := val_corr hJ h₀ (𝟙 _)
    rw [val_pull hJ, Category.id_comp, val_one] at this
    rw [val₂, e]; exact this
  let e : 𝟙_ (Over S) ⟶ G3 A := lift 1 (lift 1 1)
  have e₀ : e ≫ p₀ = 1 := by simp [e, p₀, x3]
  have e₁ : e ≫ p₁ = 1 := by simp [e, p₁, x3]
  have e₂ : e ≫ p₂ = 1 := by simp [e, p₂, x3]
  have he : e.left ≫ (A ⊗ A ⊗ A).hom = 𝟙 _ := Over.w e
  let ρ : T ⟶ G3 A := lift x (lift x' y)
  have r₀ : ρ ≫ p₀ = x := by simp [ρ, p₀, x3]
  have r₁ : ρ ≫ p₁ = x' := by simp [ρ, p₁, x3]
  have r₂ : ρ ≫ p₂ = y := by simp [ρ, p₂, x3]
  have gen : ∀ (a b a₁ b₁ a₂ b₂ k₁ k₂ k₃ l₁ l₂ l₃ : G3 A ⟶ A),
      (∀ (V : Type) [CommGroup V] (k : (G3 A ⟶ A) → V),
        (k (l₁ * l₂ * l₃) * (k (l₁ * l₂))⁻¹ * (k (l₁ * l₃))⁻¹ * (k (l₂ * l₃))⁻¹ * k l₁ * k l₂ * k l₃ * (k 1)⁻¹) *
          ((k ((a₁ ≫ f) * b₁) * (k (a₁ ≫ f))⁻¹ * (k b₁)⁻¹ * (k (a₁ * (b₁ ≫ g)))⁻¹ * k a₁ * k (b₁ ≫ g)) *
            (k ((a₂ ≫ f) * b₂) * (k (a₂ ≫ f))⁻¹ * (k b₂)⁻¹ * (k (a₂ * (b₂ ≫ g)))⁻¹ * k a₂ * k (b₂ ≫ g))) =
        (k ((a ≫ f) * b) * (k (a ≫ f))⁻¹ * (k b)⁻¹ * (k (a * (b ≫ g)))⁻¹ * k a * k (b ≫ g)) *
          (k (k₁ * k₂ * k₃) * (k (k₁ * k₂))⁻¹ * (k (k₁ * k₃))⁻¹ * (k (k₂ * k₃))⁻¹ * k k₁ * k k₂ * k k₃ * (k 1)⁻¹)) →
      e ≫ a = 1 → e ≫ b = 1 → e ≫ a₁ = 1 → e ≫ b₁ = 1 → e ≫ a₂ = 1 → e ≫ b₂ = 1 → e ≫ k₁ = 1 → e ≫ l₁ = 1 ∨ e ≫ l₂ = 1 →
      val₂ u z J (ρ ≫ a) (ρ ≫ b) * cubV c z J (ρ ≫ k₁) (ρ ≫ k₂) (ρ ≫ k₃) =
        cubV c z J (ρ ≫ l₁) (ρ ≫ l₂) (ρ ≫ l₃) * (val₂ u z J (ρ ≫ a₁) (ρ ≫ b₁) * val₂ u z J (ρ ≫ a₂) (ρ ≫ b₂)) := by
    intro a b a₁ b₁ a₂ b₂ k₁ k₂ k₃ l₁ l₂ l₃ hF ha hb ha₁ hb₁ ha₂ hb₂ hk hl
    have ev : ∀ {T' : Over S} (σ : T' ⟶ G3 A) {z : T'.left} {J}, Good Lr.L z J →
        val (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (lift a b).left)
          (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift k₁ (lift k₂ k₃)).left)) σ.left z J =
          val₂ u z J (σ ≫ a) (σ ≫ b) * cubV c z J (σ ≫ k₁) (σ ≫ k₂) (σ ≫ k₃) ∧
        val (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift l₁ (lift l₂ l₃)).left)
          (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (lift a₁ b₁).left) (LB.pullGen Lr.L _ _ u (lift a₂ b₂).left)))
          σ.left z J = cubV c z J (σ ≫ l₁) (σ ≫ l₂) (σ ≫ l₃) *
            (val₂ u z J (σ ≫ a₁) (σ ≫ b₁) * val₂ u z J (σ ≫ a₂) (σ ≫ b₂)) := fun σ z J hJ =>
      ⟨(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _) (val_cub c σ hJ _ _ _)),
        (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub c σ hJ _ _ _)
          ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _) (vp σ hJ _ _))))⟩
    refine (ev ρ hJ).1.symm.trans (Eq.trans (gen_unique' Lr.isLB (fun V _ k => ?_) _ e.left he sj
      (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hu _) (pullGen_isGen _ _ _ _ c.isGen _))
      (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ c.isGen _) (mulGen_isGen _ _ _ _ _ _ _
        (pullGen_isGen _ _ _ _ hu _) (pullGen_isGen _ _ _ _ hu _))) (fun y I hI => ?_) _ ρ.left z J hJ) (ev ρ hJ).2)
    · exact (prod_sum₂ (K := thK) (K' := Fin 6 ⊕ Fin 6) (U := V) _ (prod_cub l₁ l₂ l₃ k)
        (prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := V) _ (prod_ros f g a₁ b₁ k) (prod_ros f g a₂ b₂ k))).trans
        ((hF V fun q => k q.left).trans (prod_sum₂ (K := Fin 6) (K' := thK) (U := V) _ (prod_ros f g a b k)
          (prod_cub k₁ k₂ k₃ k)).symm)
    · have C : IsCub (cubV c y I) := isCub_cubV c hI
      refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
      rw [ha, hb, ha₁, hb₁, ha₂, hb₂, hk, v1 hI, C.face]
      rcases hl with hl | hl
      · rw [hl, C.face]; simp
      · rw [hl, C.face₂]; simp
  have o₁ : e ≫ (p₀ * p₁) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₀, e₁, _root_.mul_one])
  have s₁ : ρ ≫ (p₀ * p₁) = x * x' := (MonObj.comp_mul _ _ _).trans (by rw [r₀, r₁])
  constructor
  · have := gen (p₀ * p₁) p₂ p₀ p₂ p₁ p₂ p₀ p₁ (p₂ ≫ g) (p₀ ≫ f) (p₁ ≫ f) p₂ (fun V _ k => by
      rw [mf]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) o₁ e₂ e₀ e₂ e₁ e₂ e₀ (Or.inl (by rw [← Category.assoc, e₀, MonObj.one_comp]))
    rwa [s₁, ← Category.assoc ρ p₂, ← Category.assoc ρ p₀, ← Category.assoc ρ p₁, r₀, r₁, r₂] at this
  · have := gen p₂ (p₀ * p₁) p₂ p₀ p₂ p₁ p₂ (p₀ ≫ g) (p₁ ≫ g) (p₂ ≫ f) p₀ p₁ (fun V _ k => by
      rw [mg, _root_.mul_assoc p₂, _root_.mul_assoc (p₂ ≫ f)]
      have : (p₀ * p₁) ≫ g = (p₀ ≫ g) * (p₁ ≫ g) := mg _ _
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) e₂ o₁ e₂ e₀ e₂ e₁ e₂ (Or.inr e₀)
    rwa [s₁, ← Category.assoc ρ p₂, ← Category.assoc ρ p₀, ← Category.assoc ρ p₁, r₀, r₁, r₂] at this

theorem ros_sum_of_surj (sj : Function.Surjective (A ⊗ A).hom.appTop.hom) {f g f₁ g₁ f₂ g₂ : A ⟶ A}
    (hf : f = f₁ * f₂) (hg : g = g₁ * g₂) {u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε)}
    {u₁ : LB.Gen (LB.LinComb Lr.L (rosatiφ A f₁ g₁) rosatiε)} {u₂ : LB.Gen (LB.LinComb Lr.L (rosatiφ A f₂ g₂) rosatiε)}
    (hu : IsNormGen Lr.L f g u) (hu₁ : IsNormGen Lr.L f₁ g₁ u₁) (hu₂ : IsNormGen Lr.L f₂ g₂ u₂) {T : Over S} {z : T.left} {J}
    (hJ : Good Lr.L z J) (x w : T ⟶ A) :
    val₂ u z J x w * cubV c z J x (w ≫ g₁) (w ≫ g₂) =
      cubV c z J (x ≫ f₁) (x ≫ f₂) w * (val₂ u₁ z J x w * val₂ u₂ z J x w) := by
  subst hf hg
  have ev : ∀ {T : Over S} {z : T.left} {J}, Good Lr.L z J → ∀ x w : T ⟶ A,
      val (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (lift (fst A A) (snd A A)).left)
        (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift (fst A A) (lift (snd A A ≫ g₁) (snd A A ≫ g₂))).left))
        (lift x w).left z J = val₂ u z J x w * cubV c z J x (w ≫ g₁) (w ≫ g₂) ∧
      val (LB.mulGen Lr.L _ _ _ _
        (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift (fst A A ≫ f₁) (lift (fst A A ≫ f₂) (snd A A))).left)
        (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u₁ (lift (fst A A) (snd A A)).left)
          (LB.pullGen Lr.L _ _ u₂ (lift (fst A A) (snd A A)).left))) (lift x w).left z J =
        cubV c z J (x ≫ f₁) (x ≫ f₂) w * (val₂ u₁ z J x w * val₂ u₂ z J x w) := fun hJ x w =>
    ⟨((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull_pair u _ hJ _ _) (val_cub c _ hJ _ _ _))).trans (by
      rw [lift_snd_assoc, lift_snd_assoc, lift_fst, lift_snd]),
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub c _ hJ _ _ _) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (val_pull_pair u₁ _ hJ _ _) (val_pull_pair u₂ _ hJ _ _))))).trans (by
      rw [lift_fst_assoc, lift_fst_assoc, lift_fst, lift_snd])⟩
  refine (ev hJ x w).1.symm.trans (Eq.trans (pair_unique_of_surj sj Lr.isLB (fun U _ h => ?_)
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hu.1 _) (pullGen_isGen _ _ _ _ c.isGen _))
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ c.isGen _)
      (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hu₁.1 _) (pullGen_isGen _ _ _ _ hu₂.1 _)))
    (fun y I hI => ?_) _ hJ) (ev hJ x w).2)
  · refine (prod_sum₂ (K := thK) (K' := Fin 6 ⊕ Fin 6) (U := U) _ (prod_cub _ _ _ h)
      (prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := U) _ (prod_ros _ _ _ _ h) (prod_ros _ _ _ _ h))).trans
      (Eq.trans ?_ (prod_sum₂ (K := Fin 6) (K' := thK) (U := U) _ (prod_ros _ _ _ _ h) (prod_cub _ _ _ h)).symm)
    rw [MonObj.comp_mul, MonObj.comp_mul, _root_.mul_assoc (fst A A)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have C : IsCub (cubV c y I) := isCub_cubV c hI
    refine (ev hI 1 1).1.trans (Eq.trans ?_ (ev hI 1 1).2.symm)
    rw [hu.val_origin hI, hu₁.val_origin hI, hu₂.val_origin hI, C.face, C.face₃, _root_.mul_one, _root_.mul_one]

theorem rosati_cubical_additive : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], Function.Surjective (G ⊗ G).hom.appTop.hom → Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom → ∀ (Lr : RigLB G) (c : CubicalStr G Lr) (O : Type) [CommRing O] [StarRing O] (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G) (u : ∀ a : O, LB.Gen (LB.LinComb Lr.L (rosatiφ G (act.act a) (act.act (star a))) rosatiε)), (∀ a, (u a).IsGen ∧ LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ (u a) (zero2 G)) (LB.oneGen Lr.L)) → ∀ (T : Over S) (z : T.left) (J), Good Lr.L z J → (∀ (a : O) (x x' y : T ⟶ G), val₂ (u a) z J (x * x') y * cubV c z J x x' (y ≫ act.act (star a)) = cubV c z J (x ≫ act.act a) (x' ≫ act.act a) y * (val₂ (u a) z J x y * val₂ (u a) z J x' y)) ∧ (∀ (a : O) (x y y' : T ⟶ G), val₂ (u a) z J x (y * y') * cubV c z J x (y ≫ act.act (star a)) (y' ≫ act.act (star a)) = cubV c z J (x ≫ act.act a) y y' * (val₂ (u a) z J x y * val₂ (u a) z J x y')) ∧ (∀ (a b : O) (x y : T ⟶ G), val₂ (u (a + b)) z J x y * cubV c z J x (y ≫ act.act (star a)) (y ≫ act.act (star b)) = cubV c z J (x ≫ act.act a) (x ≫ act.act b) y * (val₂ (u a) z J x y * val₂ (u b) z J x y)) := by
  intro S G _ _ s₂ s₃ Lr c O _ _ act u hu T z J hJ
  refine ⟨fun a x x' y => ?_, fun a x y y' => ?_, fun a b x y => ?_⟩
  · have := act.hom a
    have := act.hom (star a)
    exact (ros_add_of_surj c s₃ _ _ (u a) (hu a).1 (hu a).2 hJ x x' y).1
  · have := act.hom a
    have := act.hom (star a)
    exact (ros_add_of_surj c s₃ _ _ (u a) (hu a).1 (hu a).2 hJ y y' x).2
  · exact ros_sum_of_surj c s₂ (act.add a b) (by rw [star_add, act.add]) (hu (a + b)) (hu a) (hu b) hJ x y

end GlobalTheory.RosatiCube
