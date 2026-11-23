import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentation

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Serre

variable {S : Scheme.{0}}

section Hom

variable {G H : Over S} [GrpObj G] [GrpObj H]

theorem isMonHom_of_mul_comp (f : G ⟶ H)
    (h : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f where
  one_hom := by
    rw [MonObj.one_eq_one, MonObj.one_eq_one]
    exact map_one (MonoidHom.mk' (fun x : 𝟙_ (Over S) ⟶ G ↦ x ≫ f) (h _))
  mul_hom := by
    rw [MonObj.mul_eq_mul, h, MonObj.mul_eq_mul, MonObj.comp_mul]
    simp

theorem isMonHom_mul [IsCommMonObj H] (f g : G ⟶ H) [IsMonHom f] [IsMonHom g] :
    IsMonHom (f * g) :=
  isMonHom_of_mul_comp _ fun T x y ↦ by
    simp only [MonObj.comp_mul, MonObj.mul_comp]
    exact mul_mul_mul_comm _ _ _ _

theorem isMonHom_one : IsMonHom (1 : G ⟶ H) :=
  isMonHom_of_mul_comp _ fun T x y ↦ by simp

theorem isMonHom_zpow [IsCommMonObj H] (f : G ⟶ H) [IsMonHom f] (n : ℤ) : IsMonHom (f ^ n) :=
  isMonHom_of_mul_comp _ fun T x y ↦ by
    simp only [GrpObj.comp_zpow, MonObj.mul_comp, mul_zpow]

end Hom

section Points

variable {O : Type} [CommRing O] {G H K : Over S} [GrpObj G] [GrpObj H] [GrpObj K]

theorem act_zero (a : OAct O G) : a.act 0 = 1 := by
  have := a.add 0 0
  rw [add_zero] at this
  exact mul_eq_left.mp this.symm

theorem act_comm (a : OAct O G) (c d : O) : a.act c ≫ a.act d = a.act d ≫ a.act c := by
  rw [← a.mul, ← a.mul, mul_comm]

def comapAct {O₀ : Type} [CommRing O₀] (a : OAct O G) (φ : O₀ →+* O) : OAct O₀ G where
  act c := a.act (φ c)
  hom c := a.hom _
  one := by rw [map_one, a.one]
  mul c d := by rw [map_mul, a.mul]
  add c d := by rw [map_add, a.add]

@[simp] theorem comapAct_act {O₀ : Type} [CommRing O₀] (a : OAct O G) (φ : O₀ →+* O) (c : O₀) :
    (comapAct a φ).act c = a.act (φ c) := rfl

def intAct (G : Over S) [GrpObj G] [IsCommMonObj G] : OAct ℤ G where
  act n := (𝟙 G) ^ n
  hom n := isMonHom_zpow _ n
  one := zpow_one _
  mul m n := by rw [GrpObj.comp_zpow, Category.comp_id, zpow_mul]
  add m n := zpow_add _ m n

@[simp] theorem intAct_act [IsCommMonObj G] (n : ℤ) : (intAct G).act n = (𝟙 G) ^ n := rfl

structure IsLinearHom (a : OAct O G) (b : OAct O H) (f : G ⟶ H) : Prop where

  isMonHom : IsMonHom f

  comm : ∀ c : O, a.act c ≫ f = f ≫ b.act c

theorem IsLinearHom.id (a : OAct O G) : IsLinearHom a a (𝟙 G) :=
  ⟨inferInstance, fun c ↦ by simp⟩

theorem IsLinearHom.comp {a : OAct O G} {b : OAct O H} {c : OAct O K} {f : G ⟶ H} {g : H ⟶ K}
    (hf : IsLinearHom a b f) (hg : IsLinearHom b c g) : IsLinearHom a c (f ≫ g) :=
  ⟨by have := hf.1; have := hg.1; infer_instance, fun x ↦ by
    rw [← Category.assoc, hf.comm, Category.assoc, hg.comm, Category.assoc]⟩

theorem IsLinearHom.act (a : OAct O G) (c : O) : IsLinearHom a a (a.act c) :=
  ⟨a.hom c, fun d ↦ act_comm a d c⟩

theorem IsLinearHom.mul [IsCommMonObj H] {a : OAct O G} {b : OAct O H} {f g : G ⟶ H}
    (hf : IsLinearHom a b f) (hg : IsLinearHom a b g) : IsLinearHom a b (f * g) :=
  ⟨by have := hf.1; have := hg.1; exact isMonHom_mul f g, fun c ↦ by
    have := b.hom c
    rw [MonObj.comp_mul, MonObj.mul_comp, hf.comm, hg.comm]⟩

theorem IsLinearHom.one (a : OAct O G) (b : OAct O H) : IsLinearHom a b (1 : G ⟶ H) :=
  ⟨isMonHom_one, fun c ↦ by have := b.hom c; simp⟩

theorem IsLinearHom.inv {a : OAct O G} {b : OAct O H} (e : G ≅ H) (he : IsLinearHom a b e.hom) :
    IsLinearHom b a e.inv :=
  ⟨by have := he.1; infer_instance, fun c ↦ by
    rw [Iso.comp_inv_eq, Category.assoc, he.comm, Iso.inv_hom_id_assoc]⟩

theorem IsLinearHom.int [IsCommMonObj G] [IsCommMonObj H] (f : G ⟶ H) [IsMonHom f] :
    IsLinearHom (intAct G) (intAct H) f :=
  ⟨inferInstance, fun n ↦ by simp [GrpObj.zpow_comp, GrpObj.comp_zpow]⟩

@[reducible] def pointsModule [IsCommMonObj G] (a : OAct O G) (T : Over S) :
    Module O (Additive (T ⟶ G)) where
  smul c x := Additive.ofMul (x.toMul ≫ a.act c)
  one_smul x := by
    change Additive.ofMul (x.toMul ≫ a.act 1) = x
    rw [a.one, Category.comp_id]; rfl
  mul_smul c d x := by
    change Additive.ofMul (x.toMul ≫ a.act (c * d)) =
      Additive.ofMul ((x.toMul ≫ a.act d) ≫ a.act c)
    rw [mul_comm, a.mul, Category.assoc]
  smul_zero c := by
    have := a.hom c
    exact congrArg Additive.ofMul (MonObj.one_comp (a.act c))
  smul_add c x y := by
    have := a.hom c
    exact congrArg Additive.ofMul (MonObj.mul_comp _ _ (a.act c))
  add_smul c d x := by
    change Additive.ofMul (x.toMul ≫ a.act (c + d)) =
      Additive.ofMul ((x.toMul ≫ a.act c) * (x.toMul ≫ a.act d))
    rw [a.add, MonObj.comp_mul]
  zero_smul x := by
    change Additive.ofMul (x.toMul ≫ a.act 0) = Additive.ofMul 1
    rw [act_zero, MonObj.comp_one]

@[nolint unusedArguments]
def Pts (_a : OAct O G) (T : Over S) : Type := Additive (T ⟶ G)

namespace Pts

variable {a : OAct O G} {b : OAct O H} {c : OAct O K} {T T' T'' : Over S}

def mk (a : OAct O G) : (T ⟶ G) ≃ Pts a T := Additive.ofMul

def hom (x : Pts a T) : T ⟶ G := Additive.toMul x

@[simp] theorem hom_mk (x : T ⟶ G) : (mk a x).hom = x := rfl

@[simp] theorem mk_hom (x : Pts a T) : mk a x.hom = x := rfl

@[simp] theorem mk_symm_apply (x : Pts a T) : (mk a).symm x = x.hom := rfl

@[ext] theorem ext {x y : Pts a T} (h : x.hom = y.hom) : x = y := h

variable [IsCommMonObj G] [IsCommMonObj H] [IsCommMonObj K]

instance : AddCommGroup (Pts a T) := inferInstanceAs (AddCommGroup (Additive (T ⟶ G)))

instance : Module O (Pts a T) := pointsModule a T

@[simp] theorem hom_zero : (0 : Pts a T).hom = 1 := rfl

@[simp] theorem hom_add (x y : Pts a T) : (x + y).hom = x.hom * y.hom := rfl

@[simp] theorem hom_neg (x : Pts a T) : (-x).hom = x.hom⁻¹ := rfl

@[simp] theorem hom_sub (x y : Pts a T) : (x - y).hom = x.hom / y.hom := rfl

@[simp] theorem hom_smul (r : O) (x : Pts a T) : (r • x).hom = x.hom ≫ a.act r := rfl

theorem mk_one : mk a (1 : T ⟶ G) = 0 := rfl

theorem mk_mul (x y : T ⟶ G) : mk a (x * y) = mk a x + mk a y := rfl

theorem mk_comp_act (x : T ⟶ G) (r : O) : mk a (x ≫ a.act r) = r • mk a x := rfl

@[simp] theorem hom_sum {I : Type*} (s : Finset I) (x : I → Pts a T) :
    (∑ i ∈ s, x i).hom = ∏ i ∈ s, (x i).hom := toMul_sum s x

def addEquiv (a : OAct O G) (T : Over S) : Pts a T ≃+ Additive (T ⟶ G) := AddEquiv.refl _

def pre (a : OAct O G) (u : T' ⟶ T) : Pts a T →ₗ[O] Pts a T' where
  toFun x := mk a (u ≫ x.hom)
  map_add' x y := ext (MonObj.comp_mul u x.hom y.hom)
  map_smul' r x := ext (Category.assoc u x.hom (a.act r)).symm

@[simp] theorem hom_pre (u : T' ⟶ T) (x : Pts a T) : (pre a u x).hom = u ≫ x.hom := rfl

@[simp] theorem pre_id : pre a (𝟙 T) = LinearMap.id := by ext x; simp

theorem pre_comp (v : T'' ⟶ T') (u : T' ⟶ T) : pre a (v ≫ u) = pre a v ∘ₗ pre a u := by
  ext x; simp

def post {f : G ⟶ H} (hf : IsLinearHom a b f) (T : Over S) : Pts a T →ₗ[O] Pts b T where
  toFun x := mk b (x.hom ≫ f)
  map_add' x y := ext (by have := hf.1; exact MonObj.mul_comp x.hom y.hom f)
  map_smul' r x := ext (by simp [hf.comm])

@[simp] theorem hom_post {f : G ⟶ H} (hf : IsLinearHom a b f) (x : Pts a T) :
    (post hf T x).hom = x.hom ≫ f := rfl

@[simp] theorem post_id : post (IsLinearHom.id a) T = LinearMap.id := by ext x; simp

theorem post_comp {f : G ⟶ H} {g : H ⟶ K} (hf : IsLinearHom a b f) (hg : IsLinearHom b c g) :
    post (hf.comp hg) T = post hg T ∘ₗ post hf T := by
  ext x; simp

theorem pre_post {f : G ⟶ H} (hf : IsLinearHom a b f) (u : T' ⟶ T) (x : Pts a T) :
    pre b u (post hf T x) = post hf T' (pre a u x) := by
  ext; simp

def postEquiv (e : G ≅ H) (he : IsLinearHom a b e.hom) (T : Over S) : Pts a T ≃ₗ[O] Pts b T :=
  LinearEquiv.ofLinear (post he T) (post (he.inv e) T) (by ext x; simp) (by ext x; simp)

@[simp] theorem hom_postEquiv (e : G ≅ H) (he : IsLinearHom a b e.hom) (x : Pts a T) :
    (postEquiv e he T x).hom = x.hom ≫ e.hom := rfl

@[simp] theorem hom_postEquiv_symm (e : G ≅ H) (he : IsLinearHom a b e.hom) (x : Pts b T) :
    ((postEquiv e he T).symm x).hom = x.hom ≫ e.inv := rfl

section Yoneda

variable (φ : ∀ T : Over S, Pts a T →ₗ[O] Pts b T)

def homOfNat : G ⟶ H := (φ G (mk a (𝟙 G))).hom

variable (hφ : ∀ {T T' : Over S} (u : T' ⟶ T) (x : Pts a T), φ T' (pre a u x) = pre b u (φ T x))
include hφ

theorem comp_homOfNat (x : T ⟶ G) : x ≫ homOfNat φ = (φ T (mk a x)).hom := by
  have := congrArg hom (hφ x (mk a (𝟙 G)))
  rw [hom_pre] at this
  rw [homOfNat, ← this]
  congr 2

theorem isLinearHom_homOfNat : IsLinearHom a b (homOfNat φ) where
  isMonHom := isMonHom_of_mul_comp _ fun T x y ↦ by
    simp only [comp_homOfNat φ hφ, mk_mul, map_add, hom_add]
  comm r := by
    rw [comp_homOfNat φ hφ, ← Category.id_comp (a.act r), mk_comp_act, map_smul]
    rfl

end Yoneda

end Pts

end Points

structure IsTensor {O : Type} [CommRing O] (H : Over S) [GrpObj H] [IsCommMonObj H]
    (actH : OAct O H) (G : Over S) [GrpObj G] [IsCommMonObj G] (act : OAct O G)
    (M : Type) [AddCommGroup M] [Module O M] where

  equiv : ∀ T : Over S, M ⊗[O] Pts act T ≃ₗ[O] Pts actH T

  natural : ∀ {T T' : Over S} (u : T' ⟶ T) (z : M ⊗[O] Pts act T),
    equiv T' ((Pts.pre act u).lTensor M z) = Pts.pre actH u (equiv T z)

namespace IsTensor

variable {O : Type} [CommRing O]
  {G G' G'' H H' H'' : Over S} [GrpObj G] [GrpObj G'] [GrpObj G''] [GrpObj H] [GrpObj H']
  [GrpObj H''] [IsCommMonObj G] [IsCommMonObj G'] [IsCommMonObj G''] [IsCommMonObj H]
  [IsCommMonObj H'] [IsCommMonObj H'']
  {a : OAct O G} {a' : OAct O G'} {a'' : OAct O G''} {b : OAct O H} {b' : OAct O H'}
  {b'' : OAct O H''}
  {M M' M'' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
  [AddCommGroup M''] [Module O M''] {T T' : Over S}

section Basic

variable (h : IsTensor H b G a M)

theorem natural_symm (u : T' ⟶ T) (y : Pts b T) :
    (h.equiv T').symm (Pts.pre b u y) = (Pts.pre a u).lTensor M ((h.equiv T).symm y) := by
  rw [LinearEquiv.symm_apply_eq, h.natural, LinearEquiv.apply_symm_apply]

def tmul (m : M) : G ⟶ H := (h.equiv G (m ⊗ₜ Pts.mk a (𝟙 G))).hom

@[simp] theorem hom_equiv_tmul (m : M) (x : Pts a T) :
    (h.equiv T (m ⊗ₜ x)).hom = x.hom ≫ h.tmul m := by
  have := congrArg Pts.hom (h.natural x.hom (m ⊗ₜ Pts.mk a (𝟙 G)))
  rw [Pts.hom_pre, LinearMap.lTensor_tmul] at this
  rw [tmul, ← this]
  congr 3

theorem isLinearHom_tmul (m : M) : IsLinearHom a b (h.tmul m) :=
  Pts.isLinearHom_homOfNat (fun T ↦ (h.equiv T).toLinearMap ∘ₗ TensorProduct.mk O M _ m)
    (fun u x ↦ by ext; simp)

instance isMonHom_tmul (m : M) : IsMonHom (h.tmul m) := (h.isLinearHom_tmul m).isMonHom

@[simp] theorem tmul_zero : h.tmul 0 = 1 := by simp [tmul]

theorem tmul_add (m n : M) : h.tmul (m + n) = h.tmul m * h.tmul n := by
  simp only [tmul, add_tmul, map_add, Pts.hom_add]

theorem tmul_smul (c : O) (m : M) : h.tmul (c • m) = h.tmul m ≫ b.act c := by
  simp only [tmul, ← smul_tmul', map_smul, Pts.hom_smul]

theorem tmul_smul' (c : O) (m : M) : h.tmul (c • m) = a.act c ≫ h.tmul m := by
  rw [tmul_smul, (h.isLinearHom_tmul m).comm]

def tmulLinear : M →ₗ[O] Pts b G where
  toFun m := Pts.mk b (h.tmul m)
  map_add' m n := Pts.ext (h.tmul_add m n)
  map_smul' c m := Pts.ext (h.tmul_smul c m)

@[simp] theorem hom_tmulLinear (m : M) : (h.tmulLinear m).hom = h.tmul m := rfl

theorem tmul_sum {I : Type*} (s : Finset I) (m : I → M) :
    h.tmul (∑ i ∈ s, m i) = ∏ i ∈ s, h.tmul (m i) := by
  rw [← hom_tmulLinear, map_sum, Pts.hom_sum]; rfl

theorem induction_on {P : (T ⟶ H) → Prop} (y : T ⟶ H) (one : P 1)
    (tmul : ∀ (m : M) (x : T ⟶ G), P (x ≫ h.tmul m)) (mul : ∀ y z, P y → P z → P (y * z)) :
    P y := by
  obtain ⟨z, hz⟩ := (h.equiv T).surjective (Pts.mk b y)
  have e : y = (h.equiv T z).hom := by rw [hz]; rfl
  rw [e]
  clear hz e
  induction z with
  | zero => simpa using one
  | tmul m x => simpa using tmul m x.hom
  | add z w hz hw => simpa using mul _ _ hz hw

theorem hom_ext {K : Over S} [GrpObj K] {f g : H ⟶ K} [IsMonHom f] [IsMonHom g]
    (e : ∀ m : M, h.tmul m ≫ f = h.tmul m ≫ g) : f = g := by
  rw [← Category.id_comp f, ← Category.id_comp g]
  refine h.induction_on (P := fun y ↦ y ≫ f = y ≫ g) (𝟙 H) (by simp) (fun m x ↦ ?_)
    fun y z hy hz ↦ ?_
  · simp only [Category.assoc, e]
  · simp only [MonObj.mul_comp, hy, hz]

theorem ext_tmul {h₁ h₂ : IsTensor H b G a M} (e : ∀ m, h₁.tmul m = h₂.tmul m) : h₁ = h₂ := by
  obtain ⟨e₁, n₁⟩ := h₁
  obtain ⟨e₂, n₂⟩ := h₂
  congr 1
  funext T
  refine LinearEquiv.toLinearMap_injective (TensorProduct.ext' fun m x ↦ Pts.ext ?_)
  exact ((hom_equiv_tmul ⟨e₁, n₁⟩ m x).trans (by rw [e])).trans
    (hom_equiv_tmul ⟨e₂, n₂⟩ m x).symm

def liftPts {K : Over S} [GrpObj K] [IsCommMonObj K] {c : OAct O K} (f : M →ₗ[O] Pts c G)
    (hf : ∀ m, IsLinearHom a c (f m).hom) (T : Over S) : Pts b T →ₗ[O] Pts c T :=
  TensorProduct.lift (LinearMap.mk₂ O (fun m x ↦ Pts.post (hf m) T x)
    (fun m n x ↦ by ext; simp [MonObj.comp_mul]) (fun r m x ↦ by ext; simp)
    (fun m x y ↦ map_add _ _ _) (fun r m x ↦ map_smul _ _ _)) ∘ₗ (h.equiv T).symm.toLinearMap

theorem liftPts_equiv_tmul {K : Over S} [GrpObj K] [IsCommMonObj K] {c : OAct O K}
    (f : M →ₗ[O] Pts c G) (hf : ∀ m, IsLinearHom a c (f m).hom) (m : M) (x : Pts a T) :
    (h.liftPts f hf T (h.equiv T (m ⊗ₜ x))).hom = x.hom ≫ (f m).hom := by
  simp [liftPts]

theorem liftPts_natural {K : Over S} [GrpObj K] [IsCommMonObj K] {c : OAct O K}
    (f : M →ₗ[O] Pts c G) (hf : ∀ m, IsLinearHom a c (f m).hom) (u : T' ⟶ T) (y : Pts b T) :
    h.liftPts f hf T' (Pts.pre b u y) = Pts.pre c u (h.liftPts f hf T y) := by
  obtain ⟨z, rfl⟩ := (h.equiv T).surjective y
  rw [← h.natural]
  induction z with
  | zero => simp
  | tmul m x => ext; simp [liftPts_equiv_tmul]
  | add z w hz hw => simp only [map_add, hz, hw]

def lift {K : Over S} [GrpObj K] [IsCommMonObj K] {c : OAct O K} (f : M →ₗ[O] Pts c G)
    (hf : ∀ m, IsLinearHom a c (f m).hom) : H ⟶ K :=
  Pts.homOfNat (h.liftPts f hf)

theorem isLinearHom_lift {K : Over S} [GrpObj K] [IsCommMonObj K] {c : OAct O K}
    (f : M →ₗ[O] Pts c G) (hf : ∀ m, IsLinearHom a c (f m).hom) :
    IsLinearHom b c (h.lift f hf) :=
  Pts.isLinearHom_homOfNat _ (h.liftPts_natural f hf)

@[reassoc (attr := simp)]
theorem tmul_lift {K : Over S} [GrpObj K] [IsCommMonObj K] {c : OAct O K}
    (f : M →ₗ[O] Pts c G) (hf : ∀ m, IsLinearHom a c (f m).hom) (m : M) :
    h.tmul m ≫ h.lift f hf = (f m).hom := by
  rw [lift, Pts.comp_homOfNat _ (h.liftPts_natural f hf)]
  exact (h.liftPts_equiv_tmul f hf m (Pts.mk a (𝟙 G))).trans (Category.id_comp _)

end Basic

section Map

variable (h : IsTensor H b G a M) (h' : IsTensor H' b' G' a' M') (h'' : IsTensor H'' b'' G'' a'' M'')

def map (φ : M →ₗ[O] M') {f : G ⟶ G'} (hf : IsLinearHom a a' f) : H ⟶ H' :=
  h.lift (Pts.pre b' f ∘ₗ h'.tmulLinear ∘ₗ φ) fun m ↦ hf.comp (h'.isLinearHom_tmul (φ m))

theorem isLinearHom_map (φ : M →ₗ[O] M') {f : G ⟶ G'} (hf : IsLinearHom a a' f) :
    IsLinearHom b b' (h.map h' φ hf) :=
  h.isLinearHom_lift _ _

instance isMonHom_map (φ : M →ₗ[O] M') {f : G ⟶ G'} (hf : IsLinearHom a a' f) :
    IsMonHom (h.map h' φ hf) :=
  (h.isLinearHom_map h' φ hf).isMonHom

@[reassoc (attr := simp)]
theorem tmul_map (φ : M →ₗ[O] M') {f : G ⟶ G'} (hf : IsLinearHom a a' f) (m : M) :
    h.tmul m ≫ h.map h' φ hf = f ≫ h'.tmul (φ m) :=
  h.tmul_lift _ _ m

theorem hom_equiv_comp_map (φ : M →ₗ[O] M') {f : G ⟶ G'} (hf : IsLinearHom a a' f)
    (z : M ⊗[O] Pts a T) :
    (h.equiv T z).hom ≫ h.map h' φ hf =
      (h'.equiv T (TensorProduct.map φ (Pts.post hf T) z)).hom := by
  induction z with
  | zero => simp
  | tmul m x => simp
  | add z w hz hw => simp only [map_add, Pts.hom_add, MonObj.mul_comp, hz, hw]

@[simp] theorem map_id : h.map h LinearMap.id (IsLinearHom.id a) = 𝟙 H :=
  h.hom_ext fun m ↦ by simp

theorem map_comp (φ : M →ₗ[O] M') (ψ : M' →ₗ[O] M'') {f : G ⟶ G'} (hf : IsLinearHom a a' f)
    {g : G' ⟶ G''} (hg : IsLinearHom a' a'' g) :
    h.map h'' (ψ ∘ₗ φ) (hf.comp hg) = h.map h' φ hf ≫ h'.map h'' ψ hg :=
  h.hom_ext fun m ↦ by simp

theorem map_add_left (φ ψ : M →ₗ[O] M') {f : G ⟶ G'} (hf : IsLinearHom a a' f) :
    h.map h' (φ + ψ) hf = h.map h' φ hf * h.map h' ψ hf := by
  have := isMonHom_mul (h.map h' φ hf) (h.map h' ψ hf)
  exact h.hom_ext fun m ↦ by simp [MonObj.comp_mul, tmul_add]

theorem map_mul_right (φ : M →ₗ[O] M') {f g : G ⟶ G'} (hf : IsLinearHom a a' f)
    (hg : IsLinearHom a a' g) :
    h.map h' φ (hf.mul hg) = h.map h' φ hf * h.map h' φ hg := by
  have := isMonHom_mul (h.map h' φ hf) (h.map h' φ hg)
  exact h.hom_ext fun m ↦ by simp [MonObj.comp_mul, MonObj.mul_comp]

@[simp] theorem map_zero_left {f : G ⟶ G'} (hf : IsLinearHom a a' f) : h.map h' 0 hf = 1 := by
  have := isMonHom_one (G := H) (H := H')
  exact h.hom_ext fun m ↦ by simp

theorem map_smul_left (c : O) (φ : M →ₗ[O] M') {f : G ⟶ G'} (hf : IsLinearHom a a' f) :
    h.map h' (c • φ) hf = h.map h' φ hf ≫ b'.act c := by
  have := b'.hom c
  exact h.hom_ext fun m ↦ by simp [tmul_smul]

end Map

section MapLeft

variable (h : IsTensor H b G a M) (h' : IsTensor H' b' G a M') (h'' : IsTensor H'' b'' G a M'')

def mapLeft (φ : M →ₗ[O] M') : H ⟶ H' := h.map h' φ (IsLinearHom.id a)

theorem isLinearHom_mapLeft (φ : M →ₗ[O] M') : IsLinearHom b b' (h.mapLeft h' φ) :=
  h.isLinearHom_map h' φ _

instance isMonHom_mapLeft (φ : M →ₗ[O] M') : IsMonHom (h.mapLeft h' φ) :=
  (h.isLinearHom_mapLeft h' φ).isMonHom

@[reassoc (attr := simp)]
theorem tmul_mapLeft (φ : M →ₗ[O] M') (m : M) : h.tmul m ≫ h.mapLeft h' φ = h'.tmul (φ m) := by
  simp [mapLeft]

theorem hom_equiv_comp_mapLeft (φ : M →ₗ[O] M') (z : M ⊗[O] Pts a T) :
    (h.equiv T z).hom ≫ h.mapLeft h' φ = (h'.equiv T (φ.rTensor _ z)).hom := by
  rw [mapLeft, hom_equiv_comp_map, Pts.post_id]; rfl

@[simp] theorem mapLeft_id : h.mapLeft h LinearMap.id = 𝟙 H := h.map_id

theorem mapLeft_comp (φ : M →ₗ[O] M') (ψ : M' →ₗ[O] M'') :
    h.mapLeft h'' (ψ ∘ₗ φ) = h.mapLeft h' φ ≫ h'.mapLeft h'' ψ :=
  h.hom_ext fun m ↦ by simp

theorem mapLeft_add (φ ψ : M →ₗ[O] M') :
    h.mapLeft h' (φ + ψ) = h.mapLeft h' φ * h.mapLeft h' ψ :=
  h.map_add_left h' φ ψ _

@[simp] theorem mapLeft_zero : h.mapLeft h' 0 = 1 := h.map_zero_left h' _

theorem mapLeft_smul (c : O) (φ : M →ₗ[O] M') :
    h.mapLeft h' (c • φ) = h.mapLeft h' φ ≫ b'.act c :=
  h.map_smul_left h' c φ _

theorem mapLeft_smul_id (c : O) : h.mapLeft h (c • LinearMap.id) = b.act c := by
  rw [mapLeft_smul, mapLeft_id, Category.id_comp]

def mapLeftIso (e : M ≃ₗ[O] M') : H ≅ H' where
  hom := h.mapLeft h' e
  inv := h'.mapLeft h e.symm
  hom_inv_id := h.hom_ext fun m ↦ by simp
  inv_hom_id := h'.hom_ext fun m ↦ by simp

@[simp] theorem mapLeftIso_hom (e : M ≃ₗ[O] M') : (h.mapLeftIso h' e).hom = h.mapLeft h' e := rfl

@[simp] theorem mapLeftIso_inv (e : M ≃ₗ[O] M') :
    (h.mapLeftIso h' e).inv = h'.mapLeft h e.symm := rfl

def endAct : RingAct H (Module.End O M) where
  act φ := h.mapLeft h φ
  hom φ := inferInstance
  map_one := h.mapLeft_id
  map_mul φ ψ := h.mapLeft_comp h h ψ φ
  map_add φ ψ := h.mapLeft_add h φ ψ

@[simp] theorem endAct_act (φ : Module.End O M) : h.endAct.act φ = h.mapLeft h φ := rfl

end MapLeft

section MapRight

variable (h : IsTensor H b G a M) (h' : IsTensor H' b' G' a' M) (h'' : IsTensor H'' b'' G'' a'' M)

def mapRight {f : G ⟶ G'} (hf : IsLinearHom a a' f) : H ⟶ H' := h.map h' LinearMap.id hf

theorem isLinearHom_mapRight {f : G ⟶ G'} (hf : IsLinearHom a a' f) :
    IsLinearHom b b' (h.mapRight h' hf) :=
  h.isLinearHom_map h' _ hf

instance isMonHom_mapRight {f : G ⟶ G'} (hf : IsLinearHom a a' f) :
    IsMonHom (h.mapRight h' hf) :=
  (h.isLinearHom_mapRight h' hf).isMonHom

@[reassoc (attr := simp)]
theorem tmul_mapRight {f : G ⟶ G'} (hf : IsLinearHom a a' f) (m : M) :
    h.tmul m ≫ h.mapRight h' hf = f ≫ h'.tmul m := by
  simp [mapRight]

@[simp] theorem mapRight_id : h.mapRight h (IsLinearHom.id a) = 𝟙 H := h.map_id

theorem mapRight_comp {f : G ⟶ G'} (hf : IsLinearHom a a' f) {g : G' ⟶ G''}
    (hg : IsLinearHom a' a'' g) :
    h.mapRight h'' (hf.comp hg) = h.mapRight h' hf ≫ h'.mapRight h'' hg :=
  h.hom_ext fun m ↦ by simp

theorem mapRight_mul {f g : G ⟶ G'} (hf : IsLinearHom a a' f) (hg : IsLinearHom a a' g) :
    h.mapRight h' (hf.mul hg) = h.mapRight h' hf * h.mapRight h' hg :=
  h.map_mul_right h' _ hf hg

theorem mapRight_act (c : O) : h.mapRight h (IsLinearHom.act a c) = b.act c := by
  have := b.hom c
  exact h.hom_ext fun m ↦ by simp [(h.isLinearHom_tmul m).comm]

def mapRightIso (e : G ≅ G') (he : IsLinearHom a a' e.hom) : H ≅ H' where
  hom := h.mapRight h' he
  inv := h'.mapRight h (he.inv e)
  hom_inv_id := h.hom_ext fun m ↦ by simp
  inv_hom_id := h'.hom_ext fun m ↦ by simp

end MapRight

section Unique

variable (h : IsTensor H b G a M) (h' : IsTensor H' b' G a M)

def uniqueIso : H ≅ H' := h.mapLeftIso h' (LinearEquiv.refl O M)

theorem isLinearHom_uniqueIso : IsLinearHom b b' (h.uniqueIso h').hom :=
  h.isLinearHom_mapLeft h' _

instance isMonHom_uniqueIso : IsMonHom (h.uniqueIso h').hom := (h.isLinearHom_uniqueIso h').isMonHom

@[reassoc (attr := simp)]
theorem tmul_uniqueIso_hom (m : M) : h.tmul m ≫ (h.uniqueIso h').hom = h'.tmul m :=
  h.tmul_mapLeft h' _ m

theorem hom_equiv_comp_uniqueIso (z : M ⊗[O] Pts a T) :
    (h.equiv T z).hom ≫ (h.uniqueIso h').hom = (h'.equiv T z).hom := by
  refine (h.hom_equiv_comp_mapLeft h' _ z).trans ?_
  simp

theorem eq_uniqueIso (f : H ⟶ H')
    (hf : ∀ (T : Over S) (z : M ⊗[O] Pts a T), (h.equiv T z).hom ≫ f = (h'.equiv T z).hom) :
    f = (h.uniqueIso h').hom := by
  have e := (hf H ((h.equiv H).symm (Pts.mk b (𝟙 H)))).trans
    (h.hom_equiv_comp_uniqueIso h' _).symm
  simpa using e

theorem existsUnique_iso : ∃! e : H ≅ H',
    ∀ (T : Over S) (z : M ⊗[O] Pts a T), (h.equiv T z).hom ≫ e.hom = (h'.equiv T z).hom :=
  ⟨h.uniqueIso h', fun _ z ↦ h.hom_equiv_comp_uniqueIso h' z,
    fun e he ↦ Iso.ext (h.eq_uniqueIso h' e.hom he)⟩

end Unique

section Transport

def congrLeft (h : IsTensor H b G a M) (e : M' ≃ₗ[O] M) : IsTensor H b G a M' where
  equiv T := e.rTensor (Pts a T) ≪≫ₗ h.equiv T
  natural u z := by
    simp only [LinearEquiv.trans_apply, ← h.natural]
    congr 1
    induction z with
    | zero => simp
    | tmul m x => simp
    | add z w hz hw => simp only [map_add, hz, hw]

@[simp] theorem congrLeft_tmul (h : IsTensor H b G a M) (e : M' ≃ₗ[O] M) (m : M') :
    (h.congrLeft e).tmul m = h.tmul (e m) := rfl

def congrRight (h : IsTensor H b G a M) (e : G' ≅ G) (he : IsLinearHom a' a e.hom) :
    IsTensor H b G' a' M where
  equiv T := (Pts.postEquiv e he T).lTensor M ≪≫ₗ h.equiv T
  natural u z := by
    simp only [LinearEquiv.trans_apply, ← h.natural]
    congr 1
    induction z with
    | zero => simp
    | tmul m x =>
      simp only [LinearMap.lTensor_tmul, LinearEquiv.lTensor_tmul]
      congr 1
    | add z w hz hw => simp only [map_add, hz, hw]

@[simp] theorem congrRight_tmul (h : IsTensor H b G a M) (e : G' ≅ G)
    (he : IsLinearHom a' a e.hom) (m : M) : (h.congrRight e he).tmul m = e.hom ≫ h.tmul m := by
  exact (h.hom_equiv_tmul m (Pts.postEquiv e he G' (Pts.mk a' (𝟙 G')))).trans (by simp)

def ofIso (h : IsTensor H b G a M) (e : H ≅ H') (he : IsLinearHom b b' e.hom) :
    IsTensor H' b' G a M where
  equiv T := h.equiv T ≪≫ₗ Pts.postEquiv e he T
  natural u z := by
    ext
    simp [h.natural]

@[simp] theorem ofIso_tmul (h : IsTensor H b G a M) (e : H ≅ H') (he : IsLinearHom b b' e.hom)
    (m : M) : (h.ofIso e he).tmul m = h.tmul m ≫ e.hom := rfl

def self (a : OAct O G) : IsTensor G a G a O where
  equiv T := TensorProduct.lid O (Pts a T)
  natural u z := by
    induction z with
    | zero => simp
    | tmul m x => simp
    | add z w hz hw => simp only [map_add, hz, hw]

@[simp] theorem self_tmul (a : OAct O G) (c : O) : (self a).tmul c = a.act c := by
  simp [tmul, self, -hom_equiv_tmul]

end Transport

section Algebra

variable (h : IsTensor H b G a M) (O' : Type) [CommRing O'] [Algebra O O'] [Module O' M]
  [IsScalarTower O O' M]

def algAct : OAct O' H where
  act c := h.mapLeft h (Algebra.lsmul O O M c)
  hom c := inferInstance
  one := h.hom_ext fun m ↦ by simp
  mul c d := h.hom_ext fun m ↦ by simp [smul_smul, mul_comm]
  add c d := by rw [map_add, mapLeft_add]

variable {O'}

@[reassoc (attr := simp)]
theorem tmul_algAct (c : O') (m : M) : h.tmul m ≫ (h.algAct O').act c = h.tmul (c • m) :=
  h.tmul_mapLeft h _ m

@[simp] theorem algAct_algebraMap (c : O) : (h.algAct O').act (algebraMap O O' c) = b.act c := by
  have := b.hom c
  have := (h.algAct O').hom (algebraMap O O' c)
  exact h.hom_ext fun m ↦ by simp [tmul_smul]

theorem isLinearHom_algAct (c : O') : IsLinearHom b b ((h.algAct O').act c) :=
  h.isLinearHom_mapLeft h _

variable (O') in

theorem comapAct_algAct : comapAct (h.algAct O') (algebraMap O O') = b := by
  obtain ⟨act, _, _, _, _⟩ := b
  simp only [comapAct, OAct.mk.injEq]
  exact funext fun c ↦ h.algAct_algebraMap c

variable (O') in

def algEquiv (T : Over S) : M ⊗[O] Pts a T ≃ₗ[O'] Pts (h.algAct O') T where
  toFun z := Pts.mk _ (h.equiv T z).hom
  invFun y := (h.equiv T).symm (Pts.mk b y.hom)
  map_add' z w := by ext; simp
  map_smul' c z := by
    have := (h.algAct O').hom c
    apply Pts.ext
    induction z with
    | zero => simp
    | tmul m x => simp [smul_tmul']
    | add z w hz hw =>
      simp only [Pts.hom_mk, RingHom.id_apply, Pts.hom_smul] at hz hw ⊢
      simp only [smul_add, map_add, Pts.hom_add, hz, hw, MonObj.mul_comp]
  left_inv z := by simp
  right_inv y := by simp

@[simp] theorem hom_algEquiv (z : M ⊗[O] Pts a T) :
    (h.algEquiv O' T z).hom = (h.equiv T z).hom := rfl

theorem isLinearHom_algAct_map [Module O' M'] [IsScalarTower O O' M']
    (h' : IsTensor H' b' G' a' M') (φ : M →ₗ[O'] M') {f : G ⟶ G'} (hf : IsLinearHom a a' f) :
    IsLinearHom (h.algAct O') (h'.algAct O') (h.map h' (φ.restrictScalars O) hf) :=
  ⟨inferInstance, fun c ↦ by
    have := (h.algAct O').hom c
    have := (h'.algAct O').hom c
    exact h.hom_ext fun m ↦ by simp⟩

def trans {K : Over S} [GrpObj K] [IsCommMonObj K] {c : OAct O' K} {N : Type} [AddCommGroup N]
    [Module O' N] [Module O N] [IsScalarTower O O' N]
    (k : IsTensor K c H (h.algAct O') N) :
    IsTensor K (comapAct c (algebraMap O O')) G a (N ⊗[O'] M) where
  equiv T :=
    { (AlgebraTensorModule.assoc O O' O' N M (Pts a T) ≪≫ₗ (h.algEquiv O' T).lTensor N ≪≫ₗ
        k.equiv T).toAddEquiv with
      map_smul' := fun r z ↦ by
        rw [← algebraMap_smul O' r z]
        exact map_smul (AlgebraTensorModule.assoc O O' O' N M (Pts a T) ≪≫ₗ
          (h.algEquiv O' T).lTensor N ≪≫ₗ k.equiv T) _ _ }
  natural {T T'} u z := by
    change k.equiv T' ((h.algEquiv O' T').lTensor N (AlgebraTensorModule.assoc O O' O' N M _ _)) =
      Pts.pre c u (k.equiv T ((h.algEquiv O' T).lTensor N
        (AlgebraTensorModule.assoc O O' O' N M _ z)))
    induction z with
    | zero => simp
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul w x =>
      induction w with
      | zero => simp
      | add v w hv hw => simp only [add_tmul, map_add, hv, hw]
      | tmul n m => ext; simp

@[simp] theorem trans_tmul {K : Over S} [GrpObj K] [IsCommMonObj K] {c : OAct O' K} {N : Type}
    [AddCommGroup N] [Module O' N] [Module O N] [IsScalarTower O O' N]
    (k : IsTensor K c H (h.algAct O') N) (n : N) (m : M) :
    (h.trans k).tmul (n ⊗ₜ m) = h.tmul m ≫ k.tmul n :=
  k.hom_equiv_tmul n (h.algEquiv O' G (m ⊗ₜ Pts.mk a (𝟙 G)))

end Algebra

end IsTensor

section Products

variable {O : Type} [CommRing O] {G G' H H' : Over S} [GrpObj G] [GrpObj G'] [GrpObj H] [GrpObj H']

def prodAct (b : OAct O H) (b' : OAct O H') : OAct O (H ⊗ H') where
  act c := b.act c ⊗ₘ b'.act c
  hom c := by have := b.hom c; have := b'.hom c; infer_instance
  one := by simp [b.one, b'.one]
  mul c d := by simp [b.mul, b'.mul]
  add c d := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [b.add, b'.add, MonObj.mul_comp, MonObj.comp_mul]

@[simp] theorem prodAct_act (b : OAct O H) (b' : OAct O H') (c : O) :
    (prodAct b b').act c = b.act c ⊗ₘ b'.act c := rfl

theorem isLinearHom_fst (b : OAct O H) (b' : OAct O H') : IsLinearHom (prodAct b b') b (fst H H') :=
  ⟨inferInstance, fun c ↦ by simp⟩

theorem isLinearHom_snd (b : OAct O H) (b' : OAct O H') :
    IsLinearHom (prodAct b b') b' (snd H H') :=
  ⟨inferInstance, fun c ↦ by simp⟩

theorem pow_hom_ext {n : ℕ} (p : IsPowGrp G' G n) {T : Over S} {x y : T ⟶ G'}
    (e : ∀ i, x ≫ p.pr i = y ≫ p.pr i) : x = y :=
  p.lim.hom_ext fun i ↦ e i.as

def powLift {n : ℕ} (p : IsPowGrp G' G n) {T : Over S} (x : Fin n → (T ⟶ G)) : T ⟶ G' :=
  p.lim.lift (Fan.mk T x)

@[reassoc (attr := simp)]
theorem powLift_pr {n : ℕ} (p : IsPowGrp G' G n) {T : Over S} (x : Fin n → (T ⟶ G)) (i : Fin n) :
    powLift p x ≫ p.pr i = x i :=
  p.lim.fac (Fan.mk T x) ⟨i⟩

def powAct {n : ℕ} (p : IsPowGrp G' G n) (a : OAct O G) : OAct O G' where
  act c := powLift p fun i ↦ p.pr i ≫ a.act c
  hom c := isMonHom_of_mul_comp _ fun T x y ↦ pow_hom_ext p fun i ↦ by
    have := p.hom i
    have := a.hom c
    simp [MonObj.mul_comp, MonObj.mul_comp_assoc]
  one := pow_hom_ext p fun i ↦ by simp [a.one]
  mul c d := pow_hom_ext p fun i ↦ by simp [a.mul]
  add c d := pow_hom_ext p fun i ↦ by
    have := p.hom i
    simp [a.add, MonObj.mul_comp, MonObj.comp_mul]

@[reassoc (attr := simp)]
theorem powAct_act_pr {n : ℕ} (p : IsPowGrp G' G n) (a : OAct O G) (c : O) (i : Fin n) :
    (powAct p a).act c ≫ p.pr i = p.pr i ≫ a.act c :=
  powLift_pr p _ i

theorem isLinearHom_pr {n : ℕ} (p : IsPowGrp G' G n) (a : OAct O G) (i : Fin n) :
    IsLinearHom (powAct p a) a (p.pr i) :=
  ⟨p.hom i, fun c ↦ powAct_act_pr p a c i⟩

variable [IsCommMonObj G] [IsCommMonObj G'] [IsCommMonObj H] [IsCommMonObj H']

def Pts.prodEquiv (b : OAct O H) (b' : OAct O H') (T : Over S) :
    Pts (prodAct b b') T ≃ₗ[O] Pts b T × Pts b' T where
  __ := (Pts.post (isLinearHom_fst b b') T).prod (Pts.post (isLinearHom_snd b b') T)
  invFun y := Pts.mk _ (lift y.1.hom y.2.hom)
  left_inv x := by
    apply Pts.ext
    apply CartesianMonoidalCategory.hom_ext <;> simp
  right_inv y := by ext <;> simp

@[simp] theorem Pts.hom_prodEquiv_symm (b : OAct O H) (b' : OAct O H') {T : Over S}
    (y : Pts b T × Pts b' T) : ((Pts.prodEquiv b b' T).symm y).hom = lift y.1.hom y.2.hom := rfl

def Pts.powEquiv {n : ℕ} (p : IsPowGrp G' G n) (a : OAct O G) (T : Over S) :
    Pts (powAct p a) T ≃ₗ[O] (Fin n → Pts a T) where
  __ := LinearMap.pi fun i ↦ Pts.post (isLinearHom_pr p a i) T
  invFun y := Pts.mk _ (powLift p fun i ↦ (y i).hom)
  left_inv x := Pts.ext (pow_hom_ext p fun i ↦ by simp)
  right_inv y := by ext; simp

@[simp] theorem Pts.hom_powEquiv_symm {n : ℕ} (p : IsPowGrp G' G n) (a : OAct O G) {T : Over S}
    (y : Fin n → Pts a T) : ((Pts.powEquiv p a T).symm y).hom = powLift p fun i ↦ (y i).hom := rfl

namespace IsTensor

variable {a : OAct O G} {b : OAct O H} {b' : OAct O H'} {M M' : Type} [AddCommGroup M] [Module O M]
  [AddCommGroup M'] [Module O M']

def prod (h : IsTensor H b G a M) (h' : IsTensor H' b' G a M') :
    IsTensor (H ⊗ H') (prodAct b b') G a (M × M') where
  equiv T := TensorProduct.prodLeft O O M M' (Pts a T) ≪≫ₗ (h.equiv T).prodCongr (h'.equiv T) ≪≫ₗ
    (Pts.prodEquiv b b' T).symm
  natural u z := by
    induction z with
    | zero => simp only [map_zero]
    | tmul m x =>
      obtain ⟨m, m'⟩ := m
      apply Pts.ext
      apply CartesianMonoidalCategory.hom_ext <;> simp
    | add z w hz hw => simp only [map_add, hz, hw]

@[simp] theorem prod_tmul (h : IsTensor H b G a M) (h' : IsTensor H' b' G a M') (m : M) (m' : M') :
    (h.prod h').tmul (m, m') = CartesianMonoidalCategory.lift (h.tmul m) (h'.tmul m') := rfl

def pow {n : ℕ} (p : IsPowGrp G' G n) (a : OAct O G) :
    IsTensor G' (powAct p a) G a (Fin n → O) where
  equiv T := TensorProduct.comm O _ _ ≪≫ₗ TensorProduct.piScalarRight O O (Pts a T) (Fin n) ≪≫ₗ
    (Pts.powEquiv p a T).symm
  natural u z := by
    induction z with
    | zero => simp
    | tmul m x => exact Pts.ext (pow_hom_ext p fun i ↦ by simp)
    | add z w hz hw => simp only [map_add, hz, hw]

@[reassoc (attr := simp)]
theorem pow_tmul_pr {n : ℕ} (p : IsPowGrp G' G n) (a : OAct O G) (v : Fin n → O) (i : Fin n) :
    (pow p a).tmul v ≫ p.pr i = a.act (v i) := by
  simp [tmul, pow, -hom_equiv_tmul]

theorem pow_mapLeft_pr {n k : ℕ} (p : IsPowGrp G' G n) (q : IsPowGrp H G k) (a : OAct O G)
    (A : Matrix (Fin k) (Fin n) O) (i : Fin k) :
    (pow p a).mapLeft (pow q a) (Matrix.toLin' A) ≫ q.pr i = ∏ j, p.pr j ≫ a.act (A i j) := by
  have key : ∀ (T : Over S) (y : T ⟶ G'), y ≫ ∏ j, p.pr j ≫ a.act (A i j) =
      ∏ j, y ≫ p.pr j ≫ a.act (A i j) := fun T y ↦ map_prod (preHom y) _ _
  have := q.hom i
  have : IsMonHom (∏ j, p.pr j ≫ a.act (A i j)) := isMonHom_of_mul_comp _ fun T x y ↦ by
    simp only [key, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    have := p.hom j
    have := a.hom (A i j)
    exact MonObj.mul_comp _ _ _
  refine (pow p a).hom_ext fun v ↦ ?_
  simp only [tmul_mapLeft_assoc, pow_tmul_pr, key, pow_tmul_pr_assoc, ← a.mul]
  rw [← self_tmul, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, tmul_sum]
  simp [mul_comm]

end IsTensor

end Products

section BaseChange

variable {O : Type} [CommRing O] {S' : Scheme.{0}} {G H : Over S} {G₁ H₁ : Over S'}
  [GrpObj G] [GrpObj H] [GrpObj G₁] [GrpObj H₁]

structure IsLinearPullback (a₁ : OAct O G₁) (a : OAct O G) (f : S' ⟶ S) (φ : G₁.left ⟶ G.left) :
    Prop where

  isGrpPullback : IsGrpPullback G₁ G f φ

  comm : ∀ c : O, (a₁.act c).left ≫ φ = φ ≫ (a.act c).left

theorem isLinearPullback_pullback [IsCommMonObj G] (a : OAct O G) (f : S' ⟶ S) :
    IsLinearPullback (a.pullback f G) a f (pullback.fst G.hom f) :=
  ⟨isGrpPullback_pullback G f, fun _ ↦ pullback.lift_fst _ _ _⟩

theorem IsLinearPullback.of_iso {a₁ : OAct O G₁} {b₁ : OAct O H₁} {a : OAct O G} {f : S' ⟶ S}
    {φ : G₁.left ⟶ G.left} (hφ : IsLinearPullback a₁ a f φ) (e : H₁ ≅ G₁)
    (he : IsLinearHom b₁ a₁ e.hom) : IsLinearPullback b₁ a f (e.hom.left ≫ φ) where
  isGrpPullback := by
    have := he.1
    exact ((isGrpPullback_of_iso e).comp hφ.1).congr (Category.id_comp f) rfl
  comm c := by
    rw [Category.assoc, ← hφ.comm, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
      ← Over.comp_left, he.comm]

def overBase (f : S' ⟶ S) {T T' : Over S'} (u : T' ⟶ T) :
    Over.mk (T'.hom ≫ f) ⟶ Over.mk (T.hom ≫ f) :=
  Over.homMk u.left (by
    change u.left ≫ T.hom ≫ f = T'.hom ≫ f
    rw [← Category.assoc, Over.w u])

@[simp] theorem overBase_left (f : S' ⟶ S) {T T' : Over S'} (u : T' ⟶ T) :
    (overBase f u).left = u.left := rfl

variable [IsCommMonObj G] [IsCommMonObj H] [IsCommMonObj G₁] [IsCommMonObj H₁]
  {a : OAct O G} {b : OAct O H} {a₁ : OAct O G₁} {b₁ : OAct O H₁} {f : S' ⟶ S}
  {φ : G₁.left ⟶ G.left} {ψ : H₁.left ⟶ H.left}

def Pts.pullbackEquiv (hφ : IsLinearPullback a₁ a f φ) (T : Over S') :
    Pts a₁ T ≃ₗ[O] Pts a (Over.mk (T.hom ≫ f)) where
  toFun x := Pts.mk a (pushPt hφ.1.1.w x.hom)
  invFun y := Pts.mk a₁ (Over.homMk (hφ.1.1.lift y.hom.left T.hom (Over.w y.hom))
    (hφ.1.1.lift_snd _ _ _))
  map_add' x y := Pts.ext ((pushHom hφ.1 T).map_mul x.hom y.hom)
  map_smul' c x := Pts.ext (Over.OverMorphism.ext (by
    change (x.hom.left ≫ (a₁.act c).left) ≫ φ = (x.hom.left ≫ φ) ≫ (a.act c).left
    rw [Category.assoc, hφ.comm, Category.assoc]))
  left_inv x := Pts.ext (Over.OverMorphism.ext (hφ.1.1.hom_ext (hφ.1.1.lift_fst _ _ _)
    ((hφ.1.1.lift_snd _ _ _).trans (Over.w x.hom).symm)))
  right_inv y := Pts.ext (Over.OverMorphism.ext (hφ.1.1.lift_fst _ _ _))

@[simp] theorem Pts.hom_pullbackEquiv_left (hφ : IsLinearPullback a₁ a f φ) {T : Over S'}
    (x : Pts a₁ T) : (Pts.pullbackEquiv hφ T x).hom.left = x.hom.left ≫ φ := rfl

theorem Pts.pullbackEquiv_pre (hφ : IsLinearPullback a₁ a f φ) {T T' : Over S'} (u : T' ⟶ T)
    (x : Pts a₁ T) : Pts.pullbackEquiv hφ T' (Pts.pre a₁ u x) =
      Pts.pre a (overBase f u) (Pts.pullbackEquiv hφ T x) :=
  Pts.ext (Over.OverMorphism.ext (Category.assoc u.left x.hom.left φ))

namespace IsTensor

variable {M : Type} [AddCommGroup M] [Module O M]

def baseChange (h : IsTensor H b G a M) (hφ : IsLinearPullback a₁ a f φ)
    (hψ : IsLinearPullback b₁ b f ψ) : IsTensor H₁ b₁ G₁ a₁ M where
  equiv T := (Pts.pullbackEquiv hφ T).lTensor M ≪≫ₗ h.equiv _ ≪≫ₗ (Pts.pullbackEquiv hψ T).symm
  natural {T T'} u z := by
    apply (Pts.pullbackEquiv hψ T').injective
    simp only [LinearEquiv.trans_apply, Pts.pullbackEquiv_pre, LinearEquiv.apply_symm_apply,
      ← h.natural]
    congr 1
    induction z with
    | zero => simp only [map_zero]
    | tmul m x =>
      simp only [LinearMap.lTensor_tmul, LinearEquiv.lTensor_tmul, Pts.pullbackEquiv_pre]
    | add z w hz hw => simp only [map_add, hz, hw]

theorem baseChange_tmul (h : IsTensor H b G a M) (hφ : IsLinearPullback a₁ a f φ)
    (hψ : IsLinearPullback b₁ b f ψ) (m : M) :
    ((h.baseChange hφ hψ).tmul m).left ≫ ψ = φ ≫ (h.tmul m).left := by
  have e : Pts.pullbackEquiv hψ G₁ (Pts.mk b₁ ((h.baseChange hφ hψ).tmul m)) =
      h.equiv _ (m ⊗ₜ Pts.pullbackEquiv hφ G₁ (Pts.mk a₁ (𝟙 G₁))) :=
    (Pts.pullbackEquiv hψ G₁).apply_symm_apply _
  have e' := congrArg (fun y ↦ y.hom.left) e
  simp only [Pts.hom_pullbackEquiv_left, hom_equiv_tmul, Over.comp_left, Pts.hom_mk,
    Over.id_left, Category.id_comp] at e'
  exact e'

def pullback (h : IsTensor H b G a M) (f : S' ⟶ S) :
    IsTensor ((Over.pullback f).obj H) (b.pullback f H) ((Over.pullback f).obj G)
      (a.pullback f G) M :=
  h.baseChange (isLinearPullback_pullback a f) (isLinearPullback_pullback b f)

@[simp] theorem pullback_tmul (h : IsTensor H b G a M) (f : S' ⟶ S) (m : M) :
    (h.pullback f).tmul m = (Over.pullback f).map (h.tmul m) := by
  apply Over.OverMorphism.ext
  apply (isGrpPullback_pullback H f).1.hom_ext
  · exact (h.baseChange_tmul _ _ m).trans (Limits.pullback.lift_fst _ _ _).symm
  · exact (Over.w _).trans (Over.w _).symm

theorem pullback_mapLeft {H' : Over S} [GrpObj H'] [IsCommMonObj H'] {b' : OAct O H'} {M' : Type}
    [AddCommGroup M'] [Module O M'] (h : IsTensor H b G a M) (h' : IsTensor H' b' G a M')
    (f : S' ⟶ S) (l : M →ₗ[O] M') :
    (h.pullback f).mapLeft (h'.pullback f) l = (Over.pullback f).map (h.mapLeft h' l) :=
  (h.pullback f).hom_ext fun m ↦ by
    rw [tmul_mapLeft, pullback_tmul, pullback_tmul, ← Functor.map_comp, tmul_mapLeft]

theorem exists_isLinearPullback (h : IsTensor H b G a M) (h₁ : IsTensor H₁ b₁ G₁ a₁ M)
    (hφ : IsLinearPullback a₁ a f φ) :
    ∃ ψ : H₁.left ⟶ H.left, IsLinearPullback b₁ b f ψ ∧
      ∀ m : M, (h₁.tmul m).left ≫ ψ = φ ≫ (h.tmul m).left := by
  let h₂ := h.baseChange hφ (isLinearPullback_pullback b f)
  refine ⟨_, (isLinearPullback_pullback b f).of_iso (h₁.uniqueIso h₂)
    (h₁.isLinearHom_uniqueIso h₂), fun m ↦ ?_⟩
  rw [← Category.assoc, ← Over.comp_left, tmul_uniqueIso_hom]
  exact h.baseChange_tmul hφ _ m

end IsTensor

end BaseChange

section Idempotent

variable {K : Over S} [GrpObj K]

@[reducible] def grpObjOfRetract {H : Over S} (i : H ⟶ K) (r : K ⟶ H) (hir : i ≫ r = 𝟙 H)
    [IsMonHom (r ≫ i)] : GrpObj H :=
  haveI : Mono i := (SplitMono.mk r hir).mono
  have hi : i ≫ r ≫ i = i := by rw [reassoc_of% hir]
  have h₁ : (1 ≫ r : 𝟙_ (Over S) ⟶ H) ≫ i = 1 := by rw [Category.assoc, MonObj.one_comp]
  have h₂ : ((fst H H ≫ i * snd H H ≫ i) ≫ r) ≫ i = fst H H ≫ i * snd H H ≫ i := by
    rw [Category.assoc, MonObj.mul_comp, Category.assoc, Category.assoc, hi]
  have h₃ : (i⁻¹ ≫ r) ≫ i = i⁻¹ := by rw [Category.assoc, GrpObj.inv_comp, hi]
  { one := 1 ≫ r
    mul := (fst H H ≫ i * snd H H ≫ i) ≫ r
    inv := i⁻¹ ≫ r
    one_mul := by
      rw [← cancel_mono i, Category.assoc, h₂, MonObj.comp_mul, whiskerRight_fst_assoc,
        whiskerRight_snd_assoc, h₁, MonObj.comp_one, _root_.one_mul, leftUnitor_hom]
    mul_one := by
      rw [← cancel_mono i, Category.assoc, h₂, MonObj.comp_mul, whiskerLeft_fst_assoc,
        whiskerLeft_snd_assoc, h₁, MonObj.comp_one, _root_.mul_one, rightUnitor_hom]
    mul_assoc := by
      rw [← cancel_mono i, Category.assoc, h₂, Category.assoc, Category.assoc, h₂]
      simp only [MonObj.comp_mul, whiskerRight_fst_assoc, whiskerRight_snd_assoc,
        whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, h₂]
      simp [_root_.mul_assoc]
    left_inv := by
      rw [← cancel_mono i, Category.assoc, h₂, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, h₃,
        Category.id_comp, inv_mul_cancel, Category.assoc, h₁, MonObj.comp_one]
    right_inv := by
      rw [← cancel_mono i, Category.assoc, h₂, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, h₃,
        Category.id_comp, mul_inv_cancel, Category.assoc, h₁, MonObj.comp_one] }

def fixObj {K : Over S} (p : K ⟶ K) : Over S := equalizer p (𝟙 K)

def fixIncl {K : Over S} (p : K ⟶ K) : fixObj p ⟶ K := equalizer.ι p (𝟙 K)

instance mono_fixIncl {K : Over S} (p : K ⟶ K) : Mono (fixIncl p) :=
  inferInstanceAs (Mono (equalizer.ι p (𝟙 K)))

@[reassoc (attr := simp)]
theorem fixIncl_comp {K : Over S} (p : K ⟶ K) : fixIncl p ≫ p = fixIncl p :=
  (equalizer.condition p (𝟙 K)).trans (Category.comp_id _)

def fixProj {K : Over S} {p : K ⟶ K} (hp : p ≫ p = p) : K ⟶ fixObj p :=
  equalizer.lift p (hp.trans (Category.comp_id p).symm)

@[reassoc (attr := simp)]
theorem fixProj_incl {K : Over S} {p : K ⟶ K} (hp : p ≫ p = p) : fixProj hp ≫ fixIncl p = p :=
  equalizer.lift_ι _ _

@[reassoc (attr := simp)]
theorem fixIncl_proj {K : Over S} {p : K ⟶ K} (hp : p ≫ p = p) :
    fixIncl p ≫ fixProj hp = 𝟙 _ := by
  rw [← cancel_mono (fixIncl p)]; simp

@[reducible] def fixGrp {p : K ⟶ K} [IsMonHom p] (hp : p ≫ p = p) : GrpObj (fixObj p) :=
  haveI : IsMonHom (fixProj hp ≫ fixIncl p) := by rw [fixProj_incl]; infer_instance
  grpObjOfRetract (fixIncl p) (fixProj hp) (fixIncl_proj hp)

theorem isMonHom_fixIncl {p : K ⟶ K} [IsMonHom p] (hp : p ≫ p = p) :
    letI := fixGrp hp; IsMonHom (fixIncl p) := by
  letI := fixGrp hp
  refine isMonHom_of_mul_comp _ fun T x y ↦ ?_
  change (lift x y ≫ (fst _ _ ≫ fixIncl p * snd _ _ ≫ fixIncl p) ≫ fixProj hp) ≫ fixIncl p = _
  simp [MonObj.mul_comp, MonObj.comp_mul]

theorem isMonHom_fixProj {p : K ⟶ K} [IsMonHom p] (hp : p ≫ p = p) :
    letI := fixGrp hp; IsMonHom (fixProj hp) := by
  letI := fixGrp hp
  have := isMonHom_fixIncl hp
  refine isMonHom_of_mul_comp _ fun T x y ↦ ?_
  rw [← cancel_mono (fixIncl p)]
  simp [MonObj.mul_comp]

theorem isCommMonObj_fix [IsCommMonObj K] {p : K ⟶ K} [IsMonHom p] (hp : p ≫ p = p) :
    letI := fixGrp hp; IsCommMonObj (fixObj p) := by
  letI := fixGrp hp
  have := isMonHom_fixIncl hp
  rw [isCommMonObj_iff_isMulCommutative]
  refine fun T ↦ ⟨⟨fun x y ↦ ?_⟩⟩
  rw [← cancel_mono (fixIncl p), MonObj.mul_comp, MonObj.mul_comp, mul_comm]

variable {O : Type} [CommRing O] {H : Over S} [GrpObj H]

def retractAct (c : OAct O K) (i : H ⟶ K) (r : K ⟶ H) [IsMonHom i] [IsMonHom r]
    (hir : i ≫ r = 𝟙 H) (hc : ∀ x, c.act x ≫ r ≫ i = r ≫ i ≫ c.act x) : OAct O H where
  act x := i ≫ c.act x ≫ r
  hom x := by have := c.hom x; infer_instance
  one := by rw [c.one, Category.id_comp, hir]
  mul x y := by
    simp only [c.mul, Category.assoc]
    rw [← reassoc_of% hc y, hir, Category.comp_id]
  add x y := by rw [c.add, MonObj.mul_comp, MonObj.comp_mul]

theorem isLinearHom_retract_incl (c : OAct O K) (i : H ⟶ K) (r : K ⟶ H) [IsMonHom i] [IsMonHom r]
    (hir : i ≫ r = 𝟙 H) (hc : ∀ x, c.act x ≫ r ≫ i = r ≫ i ≫ c.act x) :
    IsLinearHom (retractAct c i r hir hc) c i :=
  ⟨inferInstance, fun x ↦ by
    change (i ≫ c.act x ≫ r) ≫ i = _
    simp only [Category.assoc]
    rw [hc, reassoc_of% hir]⟩

theorem isLinearHom_retract_proj (c : OAct O K) (i : H ⟶ K) (r : K ⟶ H) [IsMonHom i] [IsMonHom r]
    (hir : i ≫ r = 𝟙 H) (hc : ∀ x, c.act x ≫ r ≫ i = r ≫ i ≫ c.act x) :
    IsLinearHom c (retractAct c i r hir hc) r :=
  ⟨inferInstance, fun x ↦ by
    change _ = r ≫ i ≫ c.act x ≫ r
    rw [← reassoc_of% hc x, hir, Category.comp_id]⟩

def IsTensor.ofRetract {G : Over S} [GrpObj G] [IsCommMonObj G] [IsCommMonObj K] [IsCommMonObj H]
    {a : OAct O G} {b : OAct O H} {c : OAct O K} {M N : Type} [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (k : IsTensor K c G a N) (s : M →ₗ[O] N) (t : N →ₗ[O] M)
    (hst : t ∘ₗ s = LinearMap.id) {i : H ⟶ K} {r : K ⟶ H} (hi : IsLinearHom b c i)
    (hr : IsLinearHom c b r) (hir : i ≫ r = 𝟙 H) (hri : r ≫ i = k.mapLeft k (s ∘ₗ t)) :
    IsTensor H b G a M where
  equiv T := LinearEquiv.ofLinear
    (Pts.post hr T ∘ₗ (k.equiv T).toLinearMap ∘ₗ s.rTensor _)
    (t.rTensor _ ∘ₗ (k.equiv T).symm.toLinearMap ∘ₗ Pts.post hi T)
    (by
      refine LinearMap.ext fun y ↦ Pts.ext ?_
      have e := k.hom_equiv_comp_mapLeft k (s ∘ₗ t) ((k.equiv T).symm (Pts.post hi T y))
      rw [LinearMap.rTensor_comp, LinearMap.comp_apply] at e
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Pts.hom_post, ← e, ← hri]
      simp [hir, reassoc_of% hir])
    (by
      refine TensorProduct.ext' fun m x ↦ ?_
      have hm : t (s m) = m := congr($hst m)
      have e : Pts.post hi T (Pts.post hr T (k.equiv T (s m ⊗ₜ x))) = k.equiv T (s m ⊗ₜ x) :=
        Pts.ext (by simp [hri, hm])
      simp [e, hm])
  natural u z := by
    change Pts.post hr _ (k.equiv _ (s.rTensor _ _)) =
      Pts.pre b u (Pts.post hr _ (k.equiv _ (s.rTensor _ z)))
    rw [Pts.pre_post, ← k.natural, ← LinearMap.comp_apply (s.rTensor _),
      ← LinearMap.comp_apply (LinearMap.lTensor _ _), LinearMap.rTensor_comp_lTensor,
      LinearMap.lTensor_comp_rTensor]

@[simp] theorem IsTensor.ofRetract_tmul {G : Over S} [GrpObj G] [IsCommMonObj G] [IsCommMonObj K]
    [IsCommMonObj H] {a : OAct O G} {b : OAct O H} {c : OAct O K} {M N : Type} [AddCommGroup M]
    [Module O M] [AddCommGroup N] [Module O N] (k : IsTensor K c G a N) (s : M →ₗ[O] N)
    (t : N →ₗ[O] M) (hst : t ∘ₗ s = LinearMap.id) {i : H ⟶ K} {r : K ⟶ H} (hi : IsLinearHom b c i)
    (hr : IsLinearHom c b r) (hir : i ≫ r = 𝟙 H) (hri : r ≫ i = k.mapLeft k (s ∘ₗ t)) (m : M) :
    (k.ofRetract s t hst hi hr hir hri).tmul m = k.tmul (s m) ≫ r := rfl

end Idempotent

section Existence

structure Summand (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] where

  n : ℕ

  incl : M →ₗ[O] (Fin n → O)

  proj : (Fin n → O) →ₗ[O] M

  proj_incl : proj ∘ₗ incl = LinearMap.id

variable {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]

def Summand.free (O : Type) [CommRing O] (n : ℕ) : Summand O (Fin n → O) :=
  ⟨n, LinearMap.id, LinearMap.id, rfl⟩

variable (O M) in

theorem Summand.nonempty [Module.Finite O M] [Module.Projective O M] : Nonempty (Summand O M) := by
  obtain ⟨n, f, g, -, -, h⟩ := Module.Finite.exists_comp_eq_id_of_projective O M
  exact ⟨⟨n, g, f, h⟩⟩

variable (O M) in

def Summand.choose [Module.Finite O M] [Module.Projective O M] : Summand O M :=
  (Summand.nonempty O M).some

variable {G : Over S} [GrpObj G] [IsCommMonObj G]

namespace Summand

variable (P : Summand O M) (a : OAct O G)

def matrix : Matrix (Fin P.n) (Fin P.n) O := LinearMap.toMatrix' (P.incl ∘ₗ P.proj)

theorem toLin'_matrix : Matrix.toLin' P.matrix = P.incl ∘ₗ P.proj := Matrix.toLin'_toMatrix' _

theorem matrix_mul_self : P.matrix * P.matrix = P.matrix := by
  rw [matrix, ← LinearMap.toMatrix'_comp, LinearMap.comp_assoc, ← LinearMap.comp_assoc _ _ P.proj,
    P.proj_incl, LinearMap.id_comp]

def idem : powObj G P.n ⟶ powObj G P.n :=
  (IsTensor.pow (powIsPowGrp G P.n) a).mapLeft (IsTensor.pow (powIsPowGrp G P.n) a)
    (P.incl ∘ₗ P.proj)

theorem idem_pr (i : Fin P.n) :
    P.idem a ≫ powPr G i = ∏ j, powPr G j ≫ a.act (P.matrix i j) := by
  rw [idem, ← toLin'_matrix]
  exact IsTensor.pow_mapLeft_pr _ (powIsPowGrp G P.n) a _ i

instance isMonHom_idem : IsMonHom (P.idem a) := IsTensor.isMonHom_mapLeft _ _ _

theorem idem_idem : P.idem a ≫ P.idem a = P.idem a := by
  rw [idem, ← IsTensor.mapLeft_comp, LinearMap.comp_assoc, ← LinearMap.comp_assoc _ _ P.proj,
    P.proj_incl, LinearMap.id_comp]

def obj : Over S := fixObj (P.idem a)

instance grpObj : GrpObj (P.obj a) := fixGrp (P.idem_idem a)

instance isCommMonObj : IsCommMonObj (P.obj a) := isCommMonObj_fix (P.idem_idem a)

def objIncl : P.obj a ⟶ powObj G P.n := fixIncl (P.idem a)

def objProj : powObj G P.n ⟶ P.obj a := fixProj (P.idem_idem a)

instance isMonHom_objIncl : IsMonHom (P.objIncl a) := isMonHom_fixIncl (P.idem_idem a)

instance isMonHom_objProj : IsMonHom (P.objProj a) := isMonHom_fixProj (P.idem_idem a)

theorem objIncl_objProj : P.objIncl a ≫ P.objProj a = 𝟙 _ := fixIncl_proj (P.idem_idem a)

theorem objProj_objIncl : P.objProj a ≫ P.objIncl a = P.idem a := fixProj_incl (P.idem_idem a)

theorem act_idem (x : O) : (powAct (powIsPowGrp G P.n) a).act x ≫ P.objProj a ≫ P.objIncl a =
    P.objProj a ≫ P.objIncl a ≫ (powAct (powIsPowGrp G P.n) a).act x := by
  rw [← Category.assoc (P.objProj a), objProj_objIncl]
  exact (IsTensor.isLinearHom_mapLeft _ _ _).comm x

def act : OAct O (P.obj a) :=
  retractAct (powAct (powIsPowGrp G P.n) a) (P.objIncl a) (P.objProj a) (P.objIncl_objProj a)
    (P.act_idem a)

def isTensor : IsTensor (P.obj a) (P.act a) G a M :=
  (IsTensor.pow (powIsPowGrp G P.n) a).ofRetract P.incl P.proj P.proj_incl
    (isLinearHom_retract_incl _ _ _ _ _) (isLinearHom_retract_proj _ _ _ _ _)
    (P.objIncl_objProj a) (P.objProj_objIncl a)

end Summand

variable (a : OAct O G) (M) [Module.Finite O M] [Module.Projective O M]

def tensorObj : Over S := (Summand.choose O M).obj a

instance tensorObj.grpObj : GrpObj (tensorObj M a) := (Summand.choose O M).grpObj a

instance tensorObj.isCommMonObj : IsCommMonObj (tensorObj M a) :=
  (Summand.choose O M).isCommMonObj a

def tensorAct : OAct O (tensorObj M a) := (Summand.choose O M).act a

def isTensor : IsTensor (tensorObj M a) (tensorAct M a) G a M := (Summand.choose O M).isTensor a

end Existence

section Properties

theorem powObj_property (P : MorphismProperty Scheme.{0}) [P.IsStableUnderComposition]
    [P.IsStableUnderBaseChange] (h₀ : P (𝟙 S)) (G : Over S) (hG : P G.hom) :
    ∀ n : ℕ, P (powObj G n).hom
  | 0 => h₀
  | n + 1 =>
    P.comp_mem _ _ (P.pullback_fst G.hom (powObj G n).hom (powObj_property P h₀ G hG n)) hG

theorem powObj_geometricallyConnected (G : Over S) [UniversallyOpen G.hom]
    [GeometricallyConnected G.hom] : ∀ n : ℕ, GeometricallyConnected (powObj G n).hom
  | 0 => inferInstanceAs (GeometricallyConnected (𝟙 S))
  | n + 1 => by
    have := powObj_geometricallyConnected G n
    have : UniversallyOpen (powObj G n).hom :=
      powObj_property @UniversallyOpen inferInstance G ‹_› n
    exact GeometricallyConnected.comp (pullback.fst G.hom (powObj G n).hom) G.hom

namespace IsTensor

variable {O : Type} [CommRing O] {G H : Over S} [GrpObj G] [GrpObj H] [IsCommMonObj G]
  [IsCommMonObj H] {a : OAct O G} {b : OAct O H} {M : Type} [AddCommGroup M] [Module O M]
  (h : IsTensor H b G a M)

def retract (P : Summand O M) : Retract H (powObj G P.n) where
  i := h.mapLeft (pow (powIsPowGrp G P.n) a) P.incl
  r := (pow (powIsPowGrp G P.n) a).mapLeft h P.proj
  retract := by rw [← mapLeft_comp, P.proj_incl, mapLeft_id]

theorem tmul_mapLeft_self (t : M →ₗ[O] O) {m : M} (hm : t m = 1) :
    h.tmul m ≫ h.mapLeft (self a) t = 𝟙 G := by
  rw [tmul_mapLeft, self_tmul, hm, a.one]

variable [Module.Finite O M] [Module.Projective O M]
include h

theorem exists_retract : ∃ (n : ℕ) (ρ : Retract H (powObj G n)), IsMonHom ρ.i ∧ IsMonHom ρ.r :=
  ⟨_, h.retract (Summand.choose O M), isMonHom_mapLeft _ _ _, isMonHom_mapLeft _ _ _⟩

theorem property (P : MorphismProperty Scheme.{0}) [P.IsStableUnderComposition]
    [P.IsStableUnderBaseChange] (h₀ : P (𝟙 S))
    (hP : ∀ {X Y : Scheme.{0}} {f : X ⟶ S} {g : Y ⟶ S} {i : X ⟶ Y} {r : Y ⟶ X},
      i ≫ r = 𝟙 X → r ≫ f = g → P g → P f) (hG : P G.hom) : P H.hom := by
  obtain ⟨n, ρ, -⟩ := h.exists_retract
  exact hP (GlobalTheory.Retract.over_left_comp ρ) (Over.w ρ.r) (powObj_property P h₀ G hG n)

theorem smooth [hG : Smooth G.hom] : Smooth H.hom :=
  h.property @Smooth inferInstance
    (fun h₁ h₂ _ ↦ GlobalTheory.Retract.smooth h₁ h₂) hG

theorem etale [hG : Etale G.hom] : Etale H.hom :=
  haveI : MorphismProperty.IsStableUnderComposition @Etale.{0} := ⟨fun _ _ _ _ ↦ inferInstance⟩
  h.property @Etale inferInstance
    (fun h₁ h₂ _ ↦ GlobalTheory.Retract.etale h₁ h₂) hG

theorem flat [hG : Flat G.hom] : Flat H.hom :=
  h.property @Flat inferInstance
    (fun h₁ h₂ _ ↦ GlobalTheory.Retract.flat h₁ h₂) hG

theorem locallyOfFiniteType [hG : LocallyOfFiniteType G.hom] : LocallyOfFiniteType H.hom :=
  h.property @LocallyOfFiniteType inferInstance
    (fun h₁ h₂ _ ↦ GlobalTheory.Retract.locallyOfFiniteType h₁ h₂) hG

theorem locallyOfFinitePresentation [hG : LocallyOfFinitePresentation G.hom] :
    LocallyOfFinitePresentation H.hom :=
  h.property @LocallyOfFinitePresentation inferInstance
    (fun h₁ h₂ _ ↦ GlobalTheory.Retract.locallyOfFinitePresentation h₁ h₂) hG

theorem quasiCompact [hG : QuasiCompact G.hom] : QuasiCompact H.hom :=
  h.property @QuasiCompact inferInstance
    (fun h₁ h₂ _ ↦ GlobalTheory.Retract.quasiCompact h₁ h₂) hG

theorem isSeparated [hG : IsSeparated G.hom] : IsSeparated H.hom :=
  h.property @IsSeparated inferInstance
    (fun h₁ h₂ _ ↦ GlobalTheory.Retract.isSeparated h₁ h₂) hG

theorem isProper [hG : IsProper G.hom] : IsProper H.hom :=
  h.property @IsProper inferInstance
    (fun h₁ h₂ _ ↦ GlobalTheory.Retract.isProper h₁ h₂) hG

theorem isAffineHom [hG : IsAffineHom G.hom] : IsAffineHom H.hom :=
  haveI : MorphismProperty.IsStableUnderComposition @IsAffineHom.{0} :=
    ⟨fun _ _ _ _ ↦ inferInstance⟩
  h.property @IsAffineHom inferInstance
    (fun h₁ h₂ _ ↦ GlobalTheory.Retract.isAffineHom h₁ h₂) hG

theorem isFinite [hG : IsFinite G.hom] : IsFinite H.hom :=
  h.property @IsFinite inferInstance
    (fun h₁ h₂ _ ↦ GlobalTheory.Retract.isFinite h₁ h₂) hG

theorem geometricallyConnected [UniversallyOpen G.hom] [GeometricallyConnected G.hom] :
    GeometricallyConnected H.hom := by
  obtain ⟨n, ρ, -⟩ := h.exists_retract
  have := powObj_geometricallyConnected G n
  exact GlobalTheory.Retract.geometricallyConnected (GlobalTheory.Retract.over_left_comp ρ) (Over.w ρ.r)

theorem isAbelianScheme (hG : IsAbelianScheme G) : IsAbelianScheme H := by
  have := hG.smooth
  have := hG.proper
  have := hG.geomConnected
  exact ⟨inferInstance, h.smooth, h.isProper, h.geometricallyConnected⟩

theorem of_isSemiAbelian (hG : IsSemiAbelian G) :
    Smooth H.hom ∧ IsSeparated H.hom ∧ QuasiCompact H.hom ∧ GeometricallyConnected H.hom := by
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  exact ⟨h.smooth, h.isSeparated, h.quasiCompact, h.geometricallyConnected⟩

theorem abLocus_subset : abLocus G ⊆ abLocus H := fun s hs K _ _ t ht ↦ by
  have : IsProper ((Over.pullback t).obj G).hom := hs K t ht
  exact (h.pullback t).isProper

end IsTensor

instance tensorObj.isAbelianScheme {O : Type} [CommRing O] {G : Over S} [GrpObj G] [IsCommMonObj G]
    (a : OAct O G) (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M]
    [Module.Projective O M] [hG : IsAbelianScheme G] : IsAbelianScheme (tensorObj M a) :=
  (isTensor M a).isAbelianScheme hG

end Properties

section Ideals

open NumberField nonZeroDivisors

variable (K : Type) {E : Type} [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]

instance finite_fractionalIdeal (I : FractionalIdeal (𝓞 E)⁰ E) : Module.Finite (𝓞 K) I :=
  have : Module.Finite (𝓞 E) I :=
    Module.Finite.iff_fg.mpr (FractionalIdeal.fg_of_isNoetherianRing le_rfl I)
  Module.Finite.trans (𝓞 E) I

instance projective_fractionalIdeal (I : FractionalIdeal (𝓞 E)⁰ E) : Module.Projective (𝓞 K) I :=
  have : Module.FinitePresentation (𝓞 K) I := Module.finitePresentation_of_finite _ _
  Module.Flat.projective_of_finitePresentation

example (A : Over S) [GrpObj A] [IsCommMonObj A] [IsAbelianScheme A] (a : OAct (𝓞 K) A)
    (I : FractionalIdeal (𝓞 E)⁰ E) :
    IsAbelianScheme (tensorObj I a) ∧ ∃ c : OAct (𝓞 E) (tensorObj I a),
      comapAct c (algebraMap (𝓞 K) (𝓞 E)) = tensorAct I a :=
  ⟨inferInstance, (isTensor I a).algAct (𝓞 E), (isTensor I a).comapAct_algAct (𝓞 E)⟩

end Ideals

section Examples

abbrev gmRat : Over (Spec (CommRingCat.of ℚ)) := splitTorusAff (CommRingCat.of ℚ) ℤ

theorem gmRat_id_ne_one : (𝟙 gmRat : gmRat ⟶ gmRat) ≠ 1 := by
  intro e
  let φ : AddMonoidAlgebra ℚ ℤ →ₐ[ℚ] AddMonoidAlgebra ℚ ℤ := AddMonoidAlgebra.lift ℚ _ ℤ 1
  let x : gmRat ⟶ gmRat := Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext φ.comp_algebraMap)
  have hx : x = 𝟙 gmRat := by rw [← Category.comp_id x, e, MonObj.comp_one]
  have h₁ : Spec.map (CommRingCat.ofHom φ.toRingHom) = Spec.map (𝟙 _) :=
    (congrArg (fun y ↦ y.left) hx).trans (Spec.map_id _).symm
  have h₂ := congrArg (fun g ↦ g.hom (AddMonoidAlgebra.single (1 : ℤ) (1 : ℚ)))
    (Spec.map_injective h₁)
  have h₃ : (1 : AddMonoidAlgebra ℚ ℤ) = AddMonoidAlgebra.single (1 : ℤ) (1 : ℚ) := by
    refine Eq.trans ?_ h₂
    change _ = φ (AddMonoidAlgebra.single (1 : ℤ) (1 : ℚ))
    rw [AddMonoidAlgebra.lift_single, MonoidHom.one_apply, one_smul]
  rw [AddMonoidAlgebra.one_def] at h₃
  exact zero_ne_one (AddMonoidAlgebra.single_left_injective one_ne_zero h₃)

def gmRatSquare : IsTensor (powObj gmRat 2) (powAct (powIsPowGrp gmRat 2) (intAct gmRat)) gmRat
    (intAct gmRat) (Fin 2 → ℤ) :=
  IsTensor.pow _ _

example : gmRatSquare.tmul ![1, -3] ≫ powPr gmRat 0 = 𝟙 gmRat ∧
    gmRatSquare.tmul ![1, -3] ≫ powPr gmRat 1 = (𝟙 gmRat) ^ (-3 : ℤ) :=
  ⟨(IsTensor.pow_tmul_pr (powIsPowGrp gmRat 2) _ _ 0).trans (by simp),
    IsTensor.pow_tmul_pr (powIsPowGrp gmRat 2) _ _ 1⟩

example : (isTensor (Fin 2 → ℤ) (intAct gmRat)).tmul ![1, 0] ≠ 1 := fun e ↦ gmRat_id_ne_one <| by
  rw [← (isTensor (Fin 2 → ℤ) (intAct gmRat)).tmul_mapLeft_self (LinearMap.proj 0)
    (m := ![1, 0]) rfl, e, MonObj.one_comp]

example (G : Over S) [GrpObj G] [IsCommMonObj G] :
    let c := (isTensor (QuadraticAlgebra ℤ (-1) 0) (intAct G)).algAct (QuadraticAlgebra ℤ (-1) 0)
    c.act ⟨0, 1⟩ ≫ c.act ⟨0, 1⟩ = (𝟙 _)⁻¹ := by
  intro c
  have e : (⟨0, 1⟩ * ⟨0, 1⟩ + 1 : QuadraticAlgebra ℤ (-1) 0) = 0 := by
    decide
  rw [← c.mul, eq_inv_iff_mul_eq_one, ← c.one, ← c.add, e, act_zero]

example {O : Type} [CommRing O] {G : Over S} [GrpObj G] [IsCommMonObj G] (a : OAct O G) :
    𝟙 (tensorObj PUnit a) = 1 := by
  have := isMonHom_one (G := tensorObj PUnit a) (H := tensorObj PUnit a)
  exact (isTensor PUnit a).hom_ext fun m ↦ by
    rw [Subsingleton.elim m 0, IsTensor.tmul_zero]; simp

end Examples

end GlobalTheory.Serre
