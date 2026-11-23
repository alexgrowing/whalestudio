import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedRingOfIntegers
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding epsScale
open GlobalTheory.GrpTangent

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Serre

section Lie

variable {R : Type} [CommRing R] {O O' O'' : Type} [CommRing O] [CommRing O'] [CommRing O'']
  {G H K : Over (Sp R)} [GrpObj G] [GrpObj H] [GrpObj K]
  [IsCommMonObj G] [IsCommMonObj H] [IsCommMonObj K]

def tangentSub (a : OAct O G) : Submodule O (Pts a (epsR R)) :=
  (LinearMap.ker (Pts.pre a (epsZero R))).copy {x | IsTangent x.hom}
    (Set.ext fun x ↦ (isTangent_iff x.hom).trans ⟨fun h ↦ Pts.ext h, fun h ↦ congrArg Pts.hom h⟩)

def Lie (a : OAct O G) : Type := tangentSub a

namespace Lie

variable {a : OAct O G} {b : OAct O' H} {c : OAct O'' K}

instance : AddCommGroup (Lie a) := inferInstanceAs (AddCommGroup (tangentSub a))

instance actModule : Module O (Lie a) := inferInstanceAs (Module O (tangentSub a))

def toPts (a : OAct O G) : Lie a →ₗ[O] Pts a (epsR R) := (tangentSub a).subtype

def hom (v : Lie a) : epsR R ⟶ G := (toPts a v).hom

@[simp] theorem hom_toPts (v : Lie a) : (toPts a v).hom = v.hom := rfl

theorem isTangent (v : Lie a) : IsTangent v.hom := v.2

def mk (a : OAct O G) (w : epsR R ⟶ G) (hw : IsTangent w) : Lie a := ⟨Pts.mk a w, hw⟩

@[simp] theorem hom_mk (w : epsR R ⟶ G) (hw : IsTangent w) : (mk a w hw).hom = w := rfl

@[ext] theorem ext {v w : Lie a} (h : v.hom = w.hom) : v = w := Subtype.ext h

def equivTangent (a : OAct O G) : Lie a ≃ {w : epsR R ⟶ G // IsTangent w} where
  toFun v := ⟨v.hom, v.isTangent⟩
  invFun w := mk a w.1 w.2
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem hom_zero : (0 : Lie a).hom = 1 := rfl

@[simp] theorem hom_add (v w : Lie a) : (v + w).hom = v.hom * w.hom := rfl

@[simp] theorem hom_neg (v : Lie a) : (-v).hom = v.hom⁻¹ := rfl

@[simp] theorem hom_act_smul (x : O) (v : Lie a) : (x • v).hom = v.hom ≫ a.act x := rfl

theorem hom_sum {I : Type*} (s : Finset I) (v : I → Lie a) :
    (∑ i ∈ s, v i).hom = ∏ i ∈ s, (v i).hom := by
  rw [← hom_toPts, map_sum, Pts.hom_sum]; rfl

instance baseModule : Module R (Lie a) where
  smul r v := mk a (epsScale r ≫ v.hom) (isTangent_epsScale r v.isTangent)
  one_smul v := ext (by
    change epsScale 1 ≫ v.hom = _
    rw [epsScale_one, Category.id_comp])
  mul_smul r s v := ext (epsScale_mul_assoc r s v.hom).symm
  smul_zero r := ext (MonObj.comp_one (epsScale r))
  smul_add r v w := ext (MonObj.comp_mul (epsScale r) v.hom w.hom)
  add_smul r s v := ext (epsScale_add_comp r s v.isTangent)
  zero_smul v := ext (epsScale_zero_comp v.isTangent)

@[simp] theorem hom_smul (r : R) (v : Lie a) : (r • v).hom = epsScale r ≫ v.hom := rfl

theorem hom_smul_left (r : R) (v : Lie a) :
    (r • v).hom.left = spMap (epsScaleR r) ≫ v.hom.left := rfl

instance smulCommClass : SMulCommClass R O (Lie a) :=
  ⟨fun r x v ↦ ext (Category.assoc (epsScale r) v.hom (a.act x)).symm⟩

instance smulCommClass' : SMulCommClass O R (Lie a) := SMulCommClass.symm _ _ _

def map (a : OAct O G) (b : OAct O' H) (f : G ⟶ H) [IsMonHom f] : Lie a →ₗ[R] Lie b where
  toFun v := mk b (v.hom ≫ f) (isTangent_comp v.isTangent f)
  map_add' v w := ext (MonObj.mul_comp v.hom w.hom f)
  map_smul' r v := ext (Category.assoc (epsScale r) v.hom f)

@[simp] theorem hom_map (f : G ⟶ H) [IsMonHom f] (v : Lie a) : (map a b f v).hom = v.hom ≫ f := rfl

@[simp] theorem map_id : map a a (𝟙 G) = LinearMap.id := by ext v; simp

theorem map_comp (f : G ⟶ H) (g : H ⟶ K) [IsMonHom f] [IsMonHom g] :
    map a c (f ≫ g) = map b c g ∘ₗ map a b f := by ext v; simp

theorem map_mul (f g : G ⟶ H) [IsMonHom f] [IsMonHom g] [IsMonHom (f * g)] :
    map a b (f * g) = map a b f + map a b g := by ext v; simp [MonObj.comp_mul]

theorem map_act (x : O) [IsMonHom (a.act x)] (v : Lie a) : map a a (a.act x) v = x • v := rfl

theorem map_act_smul {b : OAct O H} {f : G ⟶ H} [IsMonHom f] (hf : IsLinearHom a b f) (x : O)
    (v : Lie a) : map a b f (x • v) = x • map a b f v := by ext; simp [hf.comm]

def mapLinear {b : OAct O H} {f : G ⟶ H} (hf : IsLinearHom a b f) : Lie a →ₗ[O] Lie b :=
  haveI := hf.isMonHom
  { (map a b f).toAddHom with map_smul' := map_act_smul hf }

@[simp] theorem hom_mapLinear {b : OAct O H} {f : G ⟶ H} (hf : IsLinearHom a b f) (v : Lie a) :
    (mapLinear hf v).hom = v.hom ≫ f := rfl

def changeAct (a : OAct O G) (a' : OAct O' G) : Lie a ≃ₗ[R] Lie a' :=
  LinearEquiv.ofLinearMap (map a a' (𝟙 G)) (map a' a (𝟙 G)) (by ext; simp) (by ext; simp)

@[simp] theorem hom_changeAct (a' : OAct O' G) (v : Lie a) : (changeAct a a' v).hom = v.hom :=
  Category.comp_id (X := epsR R) _

def proj (a : OAct O G) : Pts a (epsR R) →ₗ[O] Lie a :=
  LinearMap.codRestrict (tangentSub a) (LinearMap.id - Pts.pre a (toUnit _ ≫ epsZero R)) fun x ↦ by
    refine (isTangent_iff _).mpr ?_
    change epsZero R ≫ (x.hom / ((toUnit _ ≫ epsZero R) ≫ x.hom)) = 1
    rw [div_eq_mul_inv, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc,
      toUnit_unique (epsZero R ≫ toUnit _) (𝟙 _), Category.id_comp, mul_inv_cancel]

theorem toPts_comp_proj :
    toPts a ∘ₗ proj a = LinearMap.id - Pts.pre a (toUnit _ ≫ epsZero R) := rfl

theorem pre_toPts (v : Lie a) : Pts.pre a (toUnit (epsR R) ≫ epsZero R) (toPts a v) = 0 :=
  Pts.ext (by
    rw [Pts.hom_pre, Category.assoc, hom_toPts, (isTangent_iff _).mp v.isTangent, MonObj.comp_one,
      Pts.hom_zero])

theorem proj_comp_toPts : proj a ∘ₗ toPts a = LinearMap.id :=
  LinearMap.ext fun v ↦ Subtype.ext (by
    change toPts a v - Pts.pre a _ (toPts a v) = toPts a v
    rw [pre_toPts, sub_zero])

theorem isLieComb_iff {n : ℕ} (r : Fin n → R) (v : Fin n → Lie a) (w : epsR R ⟶ G) :
    IsLieComb r (fun i ↦ (v i).hom) w ↔ w = (∑ i, r i • v i).hom := by
  rw [hom_sum, ← List.prod_ofFn]
  refine ⟨?_, fun h ↦ ⟨_, fun _ ↦ rfl, h⟩⟩
  rintro ⟨u, hu, rfl⟩
  obtain rfl : u = fun i ↦ (r i • v i).hom := funext fun i ↦ Over.OverMorphism.ext (hu i)
  rfl

theorem isLieBasis_iff {n : ℕ} (v : Fin n → Lie a) :
    IsLieBasis (fun i ↦ (v i).hom) ↔ Function.Bijective (Fintype.linearCombination R v) := by
  rw [Function.bijective_iff_existsUnique]
  simp only [IsLieBasis, isLieComb_iff, Fintype.linearCombination_apply]
  refine ⟨fun h w ↦ (existsUnique_congr fun r ↦ ⟨fun e ↦ ext e.symm, fun e ↦ by rw [e]⟩).mp
      (h.2 w.hom w.isTangent), fun h ↦ ⟨fun i ↦ (v i).isTangent, fun w hw ↦ ?_⟩⟩
  exact (existsUnique_congr fun r ↦ ⟨fun e ↦ by rw [e, hom_mk], fun e ↦ ext e.symm⟩).mp
    (h (mk a w hw))

def basis (a : OAct O G) {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v) :
    Module.Basis (Fin n) R (Lie a) :=
  Module.Basis.ofEquivFun
    (LinearEquiv.ofBijective _ ((isLieBasis_iff fun i ↦ mk a (v i) (hv.1 i)).mp hv)).symm

@[simp] theorem hom_basis {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v) (i : Fin n) :
    (basis a hv i).hom = v i := by
  simp [basis, Module.Basis.coe_ofEquivFun]

theorem isLieBasis_basis {n : ℕ} (v : Module.Basis (Fin n) R (Lie a)) :
    IsLieBasis fun i ↦ (v i).hom := by
  rw [isLieBasis_iff]
  convert v.equivFun.symm.bijective using 1
  ext r
  simp [Fintype.linearCombination_apply]

theorem map_kernel {i : K ⟶ G} {f : G ⟶ H} [IsMonHom i] [IsMonHom f]
    (h : IsPullback i (toUnit K) f η[H]) :
    Function.Injective (map c a i) ∧ Function.Exact (map c a i) (map a b f) := by
  have hinj : ∀ {T : Over (Sp R)} {x y : T ⟶ K}, x ≫ i = y ≫ i → x = y :=
    fun e ↦ h.hom_ext e (toUnit_unique _ _)
  refine ⟨fun v w e ↦ ext (hinj (congrArg hom e)), fun w ↦ ⟨fun e ↦ ?_, ?_⟩⟩
  · have e' : w.hom ≫ f = toUnit _ ≫ η[H] := congrArg hom e
    refine ⟨mk c (h.lift w.hom (toUnit _) e') ((isTangent_iff _).mpr (hinj ?_)),
      ext (h.lift_fst _ _ _)⟩
    rw [Category.assoc, h.lift_fst, MonObj.one_comp]
    exact (isTangent_iff _).mp w.isTangent
  · rintro ⟨v, rfl⟩
    ext
    simp only [hom_map, Category.assoc, h.w, hom_zero]
    rw [← Category.assoc, toUnit_unique (v.hom ≫ toUnit K) (toUnit _)]
    rfl

end Lie

namespace IsTensor

variable {G' H' : Over (Sp R)} [GrpObj G'] [GrpObj H'] [IsCommMonObj G'] [IsCommMonObj H']
  {a : OAct O G} {b : OAct O H} {a' : OAct O G'} {b' : OAct O H'}
  {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
  (h : IsTensor H b G a M)

def lieMap : M ⊗[O] Lie a →ₗ[O] Lie b :=
  TensorProduct.lift (LinearMap.mk₂ O (fun m v ↦ Lie.mapLinear (h.isLinearHom_tmul m) v)
    (fun m n v ↦ by ext; simp [tmul_add, MonObj.comp_mul])
    (fun x m v ↦ by ext; simp [tmul_smul]) (fun m v w ↦ map_add _ _ _) (fun x m v ↦ map_smul _ _ _))

theorem toPts_lieMap (z : M ⊗[O] Lie a) :
    Lie.toPts b (h.lieMap z) = h.equiv (epsR R) ((Lie.toPts a).lTensor M z) := by
  induction z with
  | zero => simp
  | tmul m v => ext; simp [lieMap]
  | add z w hz hw => simp only [map_add, hz, hw]

def lieEquiv : M ⊗[O] Lie a ≃ₗ[O] Lie b :=
  LinearEquiv.ofLinearMap h.lieMap
    ((Lie.proj a).lTensor M ∘ₗ (h.equiv (epsR R)).symm.toLinearMap ∘ₗ Lie.toPts b)
    (LinearMap.ext fun w ↦ Subtype.ext (by
      change Lie.toPts b (h.lieMap _) = Lie.toPts b w
      simp only [toPts_lieMap, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [← LinearMap.lTensor_comp_apply, Lie.toPts_comp_proj, LinearMap.lTensor_sub,
        LinearMap.sub_apply, ← h.natural_symm, Lie.pre_toPts]
      simp))
    (LinearMap.ext fun z ↦ by
      simp only [toPts_lieMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply]
      rw [← LinearMap.lTensor_comp_apply, Lie.proj_comp_toPts, LinearMap.lTensor_id])

@[simp] theorem hom_lieEquiv_tmul (m : M) (v : Lie a) :
    (h.lieEquiv (m ⊗ₜ v)).hom = v.hom ≫ h.tmul m := rfl

theorem toPts_lieEquiv (z : M ⊗[O] Lie a) :
    Lie.toPts b (h.lieEquiv z) = h.equiv (epsR R) ((Lie.toPts a).lTensor M z) := h.toPts_lieMap z

theorem lieEquiv_smul (r : R) (z : M ⊗[O] Lie a) :
    h.lieEquiv ((DistribSMul.toLinearMap O (Lie a) r).lTensor M z) = r • h.lieEquiv z := by
  induction z with
  | zero => simp
  | tmul m v => ext; simp
  | add z w hz hw => simp only [map_add, smul_add, hz, hw]

theorem map_lieEquiv (h' : IsTensor H' b' G' a' M') (φ : M →ₗ[O] M') {f : G ⟶ G'}
    (hf : IsLinearHom a a' f) (z : M ⊗[O] Lie a) :
    Lie.map b b' (h.map h' φ hf) (h.lieEquiv z) =
      h'.lieEquiv (TensorProduct.map φ (Lie.mapLinear hf) z) := by
  induction z with
  | zero => simp
  | tmul m v => ext; simp
  | add z w hz hw => simp only [map_add, hz, hw]

theorem mapLeft_lieEquiv (h' : IsTensor H' b' G a M') (φ : M →ₗ[O] M') (z : M ⊗[O] Lie a) :
    Lie.map b b' (h.mapLeft h' φ) (h.lieEquiv z) = h'.lieEquiv (φ.rTensor _ z) := by
  induction z with
  | zero => simp
  | tmul m v => ext; simp
  | add z w hz hw => simp only [map_add, hz, hw]

def lieEquivBase (b₁ : OAct O' H) : Lie a ⊗[O] M ≃ₗ[R] Lie b₁ :=
  ({ (TensorProduct.comm O (Lie a) M ≪≫ₗ h.lieEquiv).toAddEquiv with
    map_smul' := fun r z ↦ by
      change h.lieEquiv (TensorProduct.comm O _ _ (r • z)) =
        r • h.lieEquiv (TensorProduct.comm O _ _ z)
      induction z with
      | zero => simp
      | tmul v m => ext; simp [smul_tmul']
      | add z w hz hw => simp only [map_add, smul_add, hz, hw] } :
    Lie a ⊗[O] M ≃ₗ[R] Lie b) ≪≫ₗ Lie.changeAct b b₁

@[simp] theorem hom_lieEquivBase_tmul (b₁ : OAct O' H) (v : Lie a) (m : M) :
    (h.lieEquivBase b₁ (v ⊗ₜ m)).hom = v.hom ≫ h.tmul m :=
  Category.comp_id (X := epsR R) _

section Algebra

variable [Algebra O O'] [Module O' M] [IsScalarTower O O' M]

variable (O') in

def lieAlgEquiv : M ⊗[O] Lie a ≃ₗ[O'] Lie (h.algAct O') :=
  { h.lieEquiv.toAddEquiv.trans (Lie.changeAct b (h.algAct O')).toAddEquiv with
    map_smul' := fun x z ↦ by
      change Lie.changeAct b _ (h.lieEquiv (x • z)) = x • Lie.changeAct b _ (h.lieEquiv z)
      induction z with
      | zero => simp
      | tmul m v => ext; simp [smul_tmul']
      | add z w hz hw => simp only [map_add, smul_add, hz, hw] }

@[simp] theorem hom_lieAlgEquiv (z : M ⊗[O] Lie a) :
    (h.lieAlgEquiv O' z).hom = (h.lieEquiv z).hom :=
  Category.comp_id (X := epsR R) _

theorem lieEquivBase_smul (x : O') (z : Lie a ⊗[O] M) :
    h.lieEquivBase (h.algAct O') ((Algebra.lsmul O O M x).lTensor _ z) =
      x • h.lieEquivBase (h.algAct O') z := by
  induction z with
  | zero => simp
  | tmul v m => ext; simp
  | add z w hz hw => simp only [map_add, smul_add, hz, hw]

end Algebra

end IsTensor

end Lie

section Eigen

variable {R : Type} [CommRing R] {O O' : Type} [CommRing O] [CommRing O']
  {G H : Over (Sp R)} [GrpObj G] [GrpObj H] [IsCommMonObj G] [IsCommMonObj H]

namespace Lie

variable {a : OAct O G}

def eig (a : OAct O G) (τ : O →+* R) : Submodule R (Lie a) where
  carrier := {v | ∀ x : O, x • v = τ x • v}
  add_mem' {v w} hv hw x := by rw [smul_add, smul_add, hv, hw]
  zero_mem' x := by rw [smul_zero, smul_zero]
  smul_mem' r v hv x := by rw [smul_comm, hv, smul_comm]

theorem mem_eig_iff {τ : O →+* R} {v : Lie a} : v ∈ eig a τ ↔ ∀ x : O, x • v = τ x • v := Iff.rfl

theorem mem_eig_iff_left {τ : O →+* R} {v : Lie a} : v ∈ eig a τ ↔
    ∀ x : O, (v.hom ≫ a.act x).left = spMap (epsScaleR (τ x)) ≫ v.hom.left :=
  forall_congr' fun _ ↦ ⟨fun h ↦ congrArg (fun w : Lie a ↦ w.hom.left) h,
    fun h ↦ ext (Over.OverMorphism.ext h)⟩

theorem eig_eq_top {τ : O →+* R} {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v)
    (hτ : ∀ i x, (v i ≫ a.act x).left = spMap (epsScaleR (τ x)) ≫ (v i).left) : eig a τ = ⊤ := by
  rw [eq_top_iff, ← (basis a hv).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact mem_eig_iff_left.mpr (by simpa only [hom_basis] using hτ i)

end Lie

namespace IsTensor

variable {a : OAct O G} {b : OAct O H} {M : Type} [AddCommGroup M] [Module O M]
  (h : IsTensor H b G a M) [Algebra O R]

def lieEquivScalar (b₁ : OAct O' H) {N : Type} [AddCommGroup N] [Module R N] [Module O N]
    [IsScalarTower O R N] (e : N ≃ₗ[R] Lie a) (hτ : Lie.eig a (algebraMap O R) = ⊤) :
    N ⊗[O] M ≃ₗ[R] Lie b₁ :=
  haveI : IsScalarTower O R (Lie a) := ⟨fun x r v ↦ by
    rw [Algebra.smul_def, mul_smul, Lie.mem_eig_iff.mp (hτ.ge Submodule.mem_top) x]⟩
  AlgebraTensorModule.congr e (LinearEquiv.refl O M) ≪≫ₗ h.lieEquivBase b₁

@[simp] theorem hom_lieEquivScalar_tmul (b₁ : OAct O' H) {N : Type} [AddCommGroup N] [Module R N]
    [Module O N] [IsScalarTower O R N] (e : N ≃ₗ[R] Lie a) (hτ : Lie.eig a (algebraMap O R) = ⊤)
    (n : N) (m : M) : (h.lieEquivScalar b₁ e hτ (n ⊗ₜ m)).hom = (e n).hom ≫ h.tmul m :=
  h.hom_lieEquivBase_tmul b₁ (e n) m

def lieEquivLine (b₁ : OAct O' H) {v : epsR R ⟶ G} (hv : IsLieBasis ![v])
    (hτ : ∀ x, (v ≫ a.act x).left = spMap (epsScaleR (algebraMap O R x)) ≫ v.left) :
    R ⊗[O] M ≃ₗ[R] Lie b₁ :=
  h.lieEquivScalar b₁ ((Lie.basis a hv).equivFun ≪≫ₗ LinearEquiv.funUnique (Fin 1) R R).symm
    (Lie.eig_eq_top hv fun i ↦ by rw [Subsingleton.elim i 0]; exact hτ)

@[simp] theorem hom_lieEquivLine_tmul (b₁ : OAct O' H) {v : epsR R ⟶ G} (hv : IsLieBasis ![v])
    (hτ : ∀ x, (v ≫ a.act x).left = spMap (epsScaleR (algebraMap O R x)) ≫ v.left) (r : R) (m : M) :
    (h.lieEquivLine b₁ hv hτ (r ⊗ₜ m)).hom = epsScale r ≫ v ≫ h.tmul m := by
  simp [lieEquivLine]

variable [Algebra O O'] [Module O' M] [IsScalarTower O O' M]

theorem lieEquivLine_smul {v : epsR R ⟶ G} (hv : IsLieBasis ![v])
    (hτ : ∀ x, (v ≫ a.act x).left = spMap (epsScaleR (algebraMap O R x)) ≫ v.left) (x : O')
    (z : R ⊗[O] M) :
    h.lieEquivLine (h.algAct O') hv hτ ((Algebra.lsmul O O M x).lTensor R z) =
      x • h.lieEquivLine (h.algAct O') hv hτ z := by
  induction z with
  | zero => simp
  | tmul v m => ext; simp
  | add z w hz hw => simp only [map_add, smul_add, hz, hw]

theorem nonempty_eig_equiv [Algebra O' R] [IsScalarTower O O' R] [Module.Finite O M]
    [Module.Projective O M] [Algebra.FormallyUnramified R (R ⊗[O] O')]
    [Algebra.EssFiniteType R (R ⊗[O] O')] {N : Type} [AddCommGroup N] [Module R N] [Module O N]
    [Module O' N] [IsScalarTower O R N] [IsScalarTower O' R N] [IsScalarTower O O' N]
    (e : N ≃ₗ[R] Lie.eig a (algebraMap O R)) :
    Nonempty (N ⊗[O'] M ≃ₗ[R] Lie.eig (h.algAct O') (algebraMap O' R)) := by
  obtain ⟨s, hs₁, hs₂⟩ := exists_eigen_tensor (O := O) (O' := O') (M := M)
    ((Lie.eig a (algebraMap O R)).subtype ∘ₗ e.toLinearMap) (Subtype.val_injective.comp e.injective)
    fun l ↦ by
      rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_subtype_top]; rfl
  let F := (h.lieEquivBase (h.algAct O')).toLinearMap ∘ₗ s
  refine ⟨LinearEquiv.ofInjective F ((h.lieEquivBase _).injective.comp hs₁) ≪≫ₗ
    LinearEquiv.ofEq _ _ (Submodule.ext fun w ↦ ?_)⟩
  obtain ⟨z, rfl⟩ := (h.lieEquivBase (h.algAct O')).surjective w
  simp only [Lie.mem_eig_iff, ← h.lieEquivBase_smul, ← map_smul, EmbeddingLike.apply_eq_iff_eq,
    ← hs₂]
  exact exists_congr fun y ↦ (h.lieEquivBase (h.algAct O')).injective.eq_iff

end IsTensor

end Eigen

section Mult

variable {k : Type} [Field k] {O O' : Type} [CommRing O] [CommRing O']

theorem IsLinearPullback.id {S : Scheme.{0}} {G : Over S} [GrpObj G] (a : OAct O G) :
    IsLinearPullback a a (𝟙 S) (𝟙 G.left) :=
  haveI : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
  ⟨isGrpPullback_of_iso (Iso.refl G), fun _ ↦ by simp⟩

namespace Lie

variable {G₁ : Over (Sp k)} [GrpObj G₁] [IsCommMonObj G₁] (a₁ : OAct O G₁)

theorem iSupIndep_eig : iSupIndep (eig a₁) := by
  have h := (iSupIndep_eigen (fun x : O ↦ DistribSMul.toLinearMap k (Lie a₁) x)
    fun x y ↦ LinearMap.ext fun v ↦ smul_comm x y v).comp
      (DFunLike.coe_injective (F := O →+* k))
  refine h.mono fun τ v hv ↦ ?_
  simp only [Function.comp, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  exact hv

theorem lieMult_id_iff (τ : O →+* k) (n : ℕ) :
    LieMult a₁ (𝟙 (Sp k)) τ n ↔ Nonempty (Module.Basis (Fin n) k (eig a₁ τ)) := by
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv (IsLinearPullback.id a₁).1 (epsR k)
    (spMap (algebraMap k (DualNumber k)) ≫ 𝟙 _) rfl
  replace he : ∀ x, (e x).left = x.left := fun x ↦ (he x).trans (Category.comp_id _)
  let P (v : epsR k ⟶ G₁) : Prop := IsTangent v ∧
    ∀ x : O, (v ≫ a₁.act x).left = spMap (epsScaleR (τ x)) ≫ v.left
  have hP : ∀ v, P v ↔ IsLieEigen a₁ (𝟙 _) τ (e v) := fun v ↦ by
    have : (1 : Over.mk (𝟙 (Sp k)) ⟶ G₁).left = η[G₁].left :=
      congrArg Over.Hom.left (one_eq_one (M := G₁)).symm
    simp only [IsLieEigen, Over.comp_left, he, this]
    rfl
  have hR : ∀ (c : k) (u v : epsR k ⟶ G₁), u.left = spMap (epsScaleR c) ≫ v.left ↔
      (e u).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScale c) ≫ (e v).left := fun c u v ↦ by
    rw [he, he]; rfl
  have key : LieMult a₁ (𝟙 (Sp k)) τ n ↔ ∃ v : Fin n → (epsR k ⟶ G₁), (∀ i, P (v i)) ∧
      ∀ w, P w → ∃! c : Fin n → k, IsLieComb c v w :=
    ⟨LiePull.basis_transport e.symm (P := IsLieEigen a₁ (𝟙 _) τ) (Q := P)
      (R := fun c u v ↦ u.left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScale c) ≫ v.left)
      (R' := fun c u v ↦ u.left = spMap (epsScaleR c) ≫ v.left)
      (fun v ↦ by rw [hP, e.apply_symm_apply])
      (fun c u v ↦ by rw [hR, e.apply_symm_apply, e.apply_symm_apply]) n,
    LiePull.basis_transport e (P := P) (Q := IsLieEigen a₁ (𝟙 _) τ)
      (R := fun c u v ↦ u.left = spMap (epsScaleR c) ≫ v.left)
      (R' := fun c u v ↦ u.left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScale c) ≫ v.left) hP hR n⟩
  have comb : ∀ (v : Fin n → eig a₁ τ) (w : eig a₁ τ) (c : Fin n → k),
      IsLieComb c (fun i ↦ (v i).1.hom) w.1.hom ↔ Fintype.linearCombination k v c = w :=
    fun v w c ↦ by
      rw [isLieComb_iff, Fintype.linearCombination_apply, Subtype.ext_iff, Submodule.coe_sum]
      exact ⟨fun h ↦ ext h.symm, fun h ↦ (congrArg hom h).symm⟩
  rw [key]
  constructor
  · rintro ⟨v, hv, H⟩
    let v' (i : Fin n) : eig a₁ τ := ⟨mk a₁ (v i) (hv i).1, mem_eig_iff_left.mpr (hv i).2⟩
    exact ⟨Module.Basis.ofEquivFun (LinearEquiv.ofBijective (Fintype.linearCombination k v')
      ((Function.bijective_iff_existsUnique _).mpr fun w ↦ (existsUnique_congr (comb v' w)).mp
        (H w.1.hom ⟨w.1.isTangent, mem_eig_iff_left.mp w.2⟩))).symm⟩
  · rintro ⟨v⟩
    refine ⟨fun i ↦ (v i).1.hom, fun i ↦ ⟨(v i).1.isTangent, mem_eig_iff_left.mp (v i).2⟩,
      fun w hw ↦ (existsUnique_congr (comb v ⟨mk a₁ w hw.1, mem_eig_iff_left.mpr hw.2⟩)).mpr ?_⟩
    refine (Function.bijective_iff_existsUnique _).mp ?_ _
    convert v.equivFun.symm.bijective using 1
    ext r
    simp [Fintype.linearCombination_apply]

variable {a₁} {S : Scheme.{0}} {G : Over S} [GrpObj G] {a : OAct O G} {t : Sp k ⟶ S}
  {φ : G₁.left ⟶ G.left}

theorem lieMult_iff_basis (hφ : IsLinearPullback a₁ a t φ) (τ : O →+* k) (n : ℕ) :
    LieMult a t τ n ↔ Nonempty (Module.Basis (Fin n) k (eig a₁ τ)) := by
  rw [← lieMult_id_iff, LiePull.lieMult_pull O _ _ G G₁ t φ a a₁ hφ.1 hφ.2, Category.id_comp]

theorem lieMult_iff_finrank (hφ : IsLinearPullback a₁ a t φ) (τ : O →+* k) (n : ℕ) :
    LieMult a t τ n ↔ Module.Finite k (eig a₁ τ) ∧ Module.finrank k (eig a₁ τ) = n := by
  rw [lieMult_iff_basis hφ]
  exact ⟨fun ⟨v⟩ ↦ ⟨.of_basis v, (Module.finrank_eq_card_basis v).trans (Fintype.card_fin n)⟩,
    fun ⟨_, h⟩ ↦ ⟨Module.finBasisOfFinrankEq _ _ h⟩⟩

variable (a₁) in

theorem lieMult_of_isLieBasis {τ₀ : O →+* k} {n : ℕ} {v : Fin n → (epsR k ⟶ G₁)}
    (hv : IsLieBasis v)
    (hτ : ∀ i x, (v i ≫ a₁.act x).left = spMap (epsScaleR (τ₀ x)) ≫ (v i).left) :
    LieMult a₁ (𝟙 _) τ₀ n ∧ ∀ τ, τ ≠ τ₀ → LieMult a₁ (𝟙 _) τ 0 := by
  have h := eig_eq_top hv hτ
  refine ⟨(lieMult_id_iff _ _ _).mpr ⟨(basis a₁ hv).map (LinearEquiv.ofTop _ h).symm⟩,
    fun τ hne ↦ (lieMult_id_iff _ _ _).mpr ?_⟩
  have hd : Disjoint (eig a₁ τ) (eig a₁ τ₀) := (iSupIndep_eig a₁).pairwiseDisjoint hne
  rw [h, disjoint_top] at hd
  rw [hd]
  exact ⟨Module.Basis.empty _⟩

end Lie

namespace IsTensor

variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] [IsCommMonObj G] [IsCommMonObj H]

theorem isLinearPullback_algAct {a : OAct O G} {b : OAct O H} {M : Type} [AddCommGroup M]
    [Module O M] (h : IsTensor H b G a M) [Algebra O O'] [Module O' M] [IsScalarTower O O' M]
    {S' : Scheme.{0}} (f : S' ⟶ S) :
    IsLinearPullback ((h.pullback f).algAct O') (h.algAct O') f (pullback.fst H.hom f) :=
  ⟨isGrpPullback_pullback H f, fun _ ↦
    (congrArg (fun g ↦ g.left ≫ pullback.fst H.hom f) (h.pullback_mapLeft h f _)).trans
      (Limits.pullback.lift_fst _ _ _)⟩

theorem lieMult_of_unramified {a : OAct O G} {b : OAct O H} {M : Type} [AddCommGroup M]
    [Module O M] (h : IsTensor H b G a M) [Algebra O O'] [Module O' M] [IsScalarTower O O' M]
    [Module.Finite O M] [Module.Projective O M] [Algebra O k] [Algebra O' k] [IsScalarTower O O' k]
    [Algebra.FormallyUnramified k (k ⊗[O] O')] [Algebra.EssFiniteType k (k ⊗[O] O')]
    (t : Sp k ⟶ S) {n : ℕ} (hn : LieMult a t (algebraMap O k) n) :
    LieMult (h.algAct O') t (algebraMap O' k) (n * Module.finrank k (k ⊗[O'] M)) := by
  obtain ⟨v⟩ := (Lie.lieMult_iff_basis (isLinearPullback_pullback a t) _ _).mp hn
  obtain ⟨e⟩ := (h.pullback t).nonempty_eig_equiv (O' := O') v.equivFun.symm
  have : Module.Finite O' M := .of_restrictScalars_finite O O' M
  let e' := AlgebraTensorModule.cancelBaseChange O' k k (Fin n → k) M ≪≫ₗ e
  rw [Lie.lieMult_iff_finrank (h.isLinearPullback_algAct t)]
  refine ⟨.equiv e', ?_⟩
  rw [← e'.finrank_eq, Module.finrank_tensorProduct, Module.finrank_fin_fun]

open NumberField

variable [CharZero k] {K E : Type} [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
  {a : OAct (𝓞 K) G} {b : OAct (𝓞 K) H}

section Module

variable {M : Type} [AddCommGroup M] [Module (𝓞 K) M] [Module (𝓞 E) M]
  [IsScalarTower (𝓞 K) (𝓞 E) M] [Module.Finite (𝓞 E) M] [Module.Projective (𝓞 E) M]
  (h : IsTensor H b G a M)

theorem lieMult (t : Sp k ⟶ S) (τ : 𝓞 E →+* k) {n : ℕ}
    (hn : LieMult a t (τ.comp (algebraMap (𝓞 K) (𝓞 E))) n) :
    LieMult (h.algAct (𝓞 E)) t τ (n * Module.finrank (𝓞 E) M) := by
  let : Algebra (𝓞 E) k := τ.toAlgebra
  let : Algebra (𝓞 K) k := (τ.comp (algebraMap (𝓞 K) (𝓞 E))).toAlgebra
  have : IsScalarTower (𝓞 K) (𝓞 E) k := .of_algebraMap_eq' rfl
  have := formallyUnramified_ringOfIntegers k K E
  have : Module.Finite (𝓞 K) M := .trans (𝓞 E) M
  have : Module.Flat (𝓞 K) M := .trans (𝓞 K) (𝓞 E) M
  have : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) M := Module.Flat.projective_of_finitePresentation
  have : FaithfulSMul (𝓞 E) k :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (ringOfIntegers_injective k E τ)
  rw [← (TensorProduct.isBaseChange (𝓞 E) M k).finrank_eq]
  exact h.lieMult_of_unramified t hn

theorem detCond [IsCMField E] {X : Host E} (D : Datum X) (t : Sp k ⟶ S) (ρ : k) (r : 𝓞 K)
    (hr : algebraMap (𝓞 K) (𝓞 E) r = X.rt) {p₀ q₀ : ℕ}
    (hG : ∀ σ : 𝓞 K →+* k, (σ r = ρ → LieMult a t σ p₀) ∧ (σ r ≠ ρ → LieMult a t σ q₀))
    (hp : D.p = p₀ * Module.finrank (𝓞 E) M) (hq : D.q = q₀ * Module.finrank (𝓞 E) M) :
    DetCond D (h.algAct (𝓞 E)) t ρ := fun τ ↦ by
  rw [hp, hq, ← hr]
  exact ⟨fun e ↦ h.lieMult t τ ((hG _).1 e), fun e ↦ h.lieMult t τ ((hG _).2 e)⟩

theorem detCond_line {G₁ H₁ : Over (Sp k)} [GrpObj G₁] [GrpObj H₁] [IsCommMonObj G₁]
    [IsCommMonObj H₁] {a₁ : OAct (𝓞 K) G₁} {b₁ : OAct (𝓞 K) H₁} (h : IsTensor H₁ b₁ G₁ a₁ M)
    [IsCMField E] {X : Host E} (D : Datum X) (r : 𝓞 K) (hr : algebraMap (𝓞 K) (𝓞 E) r = X.rt)
    (hK : Algebra.adjoin ℚ {(r : K)} = ⊤) {τ₀ : 𝓞 K →+* k} {v : epsR k ⟶ G₁} (hv : IsLieBasis ![v])
    (hτ : ∀ x, (v ≫ a₁.act x).left = spMap (epsScaleR (τ₀ x)) ≫ v.left)
    (hp : D.p = Module.finrank (𝓞 E) M) (hq : D.q = 0) :
    DetCond D (h.algAct (𝓞 E)) (𝟙 _) (τ₀ r) := by
  have H := Lie.lieMult_of_isLieBasis a₁ hv (τ₀ := τ₀) fun i ↦ by
    rw [Subsingleton.elim i 0]; exact hτ
  refine h.detCond D _ _ r hr (p₀ := 1) (q₀ := 0) (fun σ ↦ ⟨fun e ↦ ?_, fun e ↦ H.2 σ ?_⟩)
    (by rw [hp, _root_.one_mul]) (by rw [hq, zero_mul])
  · let l (σ : 𝓞 K →+* k) : K →ₐ[ℚ] k :=
      (IsFractionRing.lift (ringOfIntegers_injective k K σ)).toRatAlgHom
    have hl : ∀ σ (x : 𝓞 K), l σ x = σ x := fun σ x ↦
      IsFractionRing.lift_algebraMap (ringOfIntegers_injective k K σ) x
    have : l σ = l τ₀ := AlgHom.ext_of_adjoin_eq_top hK fun x hx ↦ by
      rw [Set.mem_singleton_iff.mp hx, hl, hl, e]
    obtain rfl : σ = τ₀ := RingHom.ext fun x ↦ by rw [← hl, this, hl]
    exact H.1
  · rintro rfl
    exact e rfl

end Module

section Ideal

variable {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E}

theorem lieMult_fractionalIdeal (h : IsTensor H b G a I) (hI : I ≠ 0) (t : Sp k ⟶ S)
    (τ : 𝓞 E →+* k) {n : ℕ} (hn : LieMult a t (τ.comp (algebraMap (𝓞 K) (𝓞 E))) n) :
    LieMult (h.algAct (𝓞 E)) t τ n := by
  simpa only [finrank_fractionalIdeal E hI, _root_.mul_one] using h.lieMult t τ hn

variable {G₁ H₁ : Over (Sp k)} [GrpObj G₁] [GrpObj H₁] [IsCommMonObj G₁] [IsCommMonObj H₁]
  {a₁ : OAct (𝓞 K) G₁} {b₁ : OAct (𝓞 K) H₁}

theorem lieMult_line (h : IsTensor H₁ b₁ G₁ a₁ I) (hI : I ≠ 0) {τ₀ : 𝓞 K →+* k}
    {v : epsR k ⟶ G₁} (hv : IsLieBasis ![v])
    (hτ : ∀ x, (v ≫ a₁.act x).left = spMap (epsScaleR (τ₀ x)) ≫ v.left) (τ : 𝓞 E →+* k) :
    (τ.comp (algebraMap (𝓞 K) (𝓞 E)) = τ₀ → LieMult (h.algAct (𝓞 E)) (𝟙 _) τ 1) ∧
      (τ.comp (algebraMap (𝓞 K) (𝓞 E)) ≠ τ₀ → LieMult (h.algAct (𝓞 E)) (𝟙 _) τ 0) := by
  have H := Lie.lieMult_of_isLieBasis a₁ hv (τ₀ := τ₀) fun i ↦ by
    rw [Subsingleton.elim i 0]; exact hτ
  exact ⟨fun e ↦ h.lieMult_fractionalIdeal hI _ τ (e ▸ H.1),
    fun e ↦ h.lieMult_fractionalIdeal hI _ τ (H.2 _ e)⟩

theorem isInternal_eig [Algebra K k] [DecidableEq (E →ₐ[K] k)] (h : IsTensor H₁ b₁ G₁ a₁ I)
    (hI : I ≠ 0) (hk : ∀ x : E, ((minpoly K x).map (algebraMap K k)).Splits)
    {v : epsR k ⟶ G₁} (hv : IsLieBasis ![v])
    (hτ : ∀ x : 𝓞 K, (v ≫ a₁.act x).left = spMap (epsScaleR (algebraMap K k x)) ≫ v.left) :
    DirectSum.IsInternal fun σ : E →ₐ[K] k ↦
      Lie.eig (h.algAct (𝓞 E)) ((σ : E →+* k).comp (algebraMap (𝓞 E) E)) := by
  let r (σ : E →ₐ[K] k) : 𝓞 E →+* k := (σ : E →+* k).comp (algebraMap (𝓞 E) E)
  have hr : Function.Injective r := fun σ σ' e ↦ AlgHom.coe_ringHom_injective
    (IsFractionRing.ringHom_ext (A := 𝓞 E) fun x ↦ congr($e x))
  have hind : iSupIndep fun σ ↦ Lie.eig (h.algAct (𝓞 E)) (r σ) := (Lie.iSupIndep_eig _).comp hr
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind ?_
  have hw : ∀ σ, ∃ w ∈ Lie.eig (h.algAct (𝓞 E)) (r σ), w ≠ 0 := fun σ ↦ by
    obtain ⟨u⟩ := (Lie.lieMult_id_iff _ _ _).mp ((h.lieMult_line hI
      (τ₀ := (algebraMap K k).comp (algebraMap (𝓞 K) K)) hv hτ (r σ)).1
        (RingHom.ext fun x ↦ σ.commutes x))
    exact ⟨u 0, (u 0).2, fun e ↦ u.ne_zero 0 (Subtype.ext e)⟩
  choose w hw hw₀ using hw
  let : Algebra (𝓞 K) k := ((algebraMap K k).comp (algebraMap (𝓞 K) K)).toAlgebra
  have : FaithfulSMul (𝓞 K) k :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (ringOfIntegers_injective k K _)
  let e := h.lieEquivLine (h.algAct (𝓞 E)) hv hτ
  have : Module.Finite k (Lie (h.algAct (𝓞 E))) := .equiv e
  have hspan := (hind.linearIndependent _ hw hw₀).span_eq_top_of_card_eq_finrank' (by
    rw [AlgHom.card_of_splits K E k hk, ← e.finrank_eq,
      (TensorProduct.isBaseChange (𝓞 K) I k).finrank_eq, finrank_fractionalIdeal_restrict K E hI])
  rw [eq_top_iff, ← hspan, Submodule.span_le]
  rintro _ ⟨σ, rfl⟩
  exact Submodule.mem_iSup_of_mem σ (hw σ)

end Ideal

end IsTensor

end Mult

def Lie.splitTorusEquiv {R O X : Type} [CommRing R] [CommRing O] [AddCommGroup X]
    (a : OAct O (ReciprocityTheory.ChartRestriction.G.Semi.splitTorus (Sp R) X)) : (X →+ R) ≃ₗ[R] Lie a :=
  LinearEquiv.ofBijective
    ({ toFun c := Lie.mk a (Diag.lieVec c) (Diag.isTangent_lieVec c)
       map_add' c d := Lie.ext (Diag.lieVec_add c d)
       map_smul' r c := Lie.ext (Diag.lieVec_smul r c) } : (X →+ R) →ₗ[R] Lie a)
    ⟨fun _ _ e ↦ Diag.lieVec_injective (congrArg Lie.hom e), fun v ↦
      ((Diag.isTangent_iff_exists _).mp v.isTangent).imp fun _ e ↦ Lie.ext e⟩

example : Module.finrank ℚ
    (Lie (tensorAct (Fin 2 → ℤ) (intAct (ReciprocityTheory.ChartRestriction.G.Semi.splitTorus (Sp ℚ) ℤ)))) = 2 := by
  have e := (isTensor (Fin 2 → ℤ) (intAct (ReciprocityTheory.ChartRestriction.G.Semi.splitTorus (Sp ℚ) ℤ))).lieEquivScalar
    (tensorAct (Fin 2 → ℤ) _) (N := ℚ)
    ((addMonoidHomLequivInt ℚ ≪≫ₗ LinearMap.ringLmapEquivSelf ℤ ℚ ℚ).symm ≪≫ₗ
      Lie.splitTorusEquiv _) (by
      refine eq_top_iff.mpr fun v _ x ↦ ?_
      rw [algebraMap_int_eq, eq_intCast, Int.cast_smul_eq_zsmul]
      exact int_smul_eq_zsmul Lie.actModule x v)
  rw [← e.finrank_eq, Module.finrank_baseChange, Module.finrank_fin_fun]

open NumberField in

theorem lie_tensor :
    (∀ (R O : Type) [CommRing R] [CommRing O] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
      (a : OAct O G),
      (∀ w : epsR R ⟶ G, IsTangent w ↔ ∃ v : Lie a, v.hom = w) ∧
      Function.Injective (Lie.hom : Lie a → _) ∧
      (∀ v w : Lie a, (v + w).hom = v.hom * w.hom) ∧
      (∀ (r : R) (v : Lie a), (r • v).hom.left = spMap (epsScaleR r) ≫ v.hom.left) ∧
      (∀ (x : O) (v : Lie a), (x • v).hom = v.hom ≫ a.act x) ∧
      (∀ (r : R) (x : O) (v : Lie a), r • x • v = x • r • v) ∧
      (∀ (n : ℕ) (v : Fin n → (epsR R ⟶ G)),
        IsLieBasis v ↔ ∃ u : Module.Basis (Fin n) R (Lie a), ∀ i, (u i).hom = v i) ∧
      ∀ (H K : Over (Sp R)) [GrpObj H] [IsCommMonObj H] [GrpObj K] [IsCommMonObj K] (b : OAct O H)
        (c : OAct O K) (i : K ⟶ G) (f : G ⟶ H) [IsMonHom i] [IsMonHom f],
        IsPullback i (toUnit K) f η[H] →
          Function.Injective (Lie.map c a i) ∧ Function.Exact (Lie.map c a i) (Lie.map a b f)) ∧
    (∀ (R O : Type) [CommRing R] [CommRing O] (G H : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
      [GrpObj H] [IsCommMonObj H] (a : OAct O G) (b : OAct O H) (M : Type) [AddCommGroup M]
      [Module O M] (h : IsTensor H b G a M),
      (∀ (m : M) (v : Lie a), (h.lieEquiv (m ⊗ₜ v)).hom = v.hom ≫ h.tmul m) ∧
      (∀ (r : R) (z : M ⊗[O] Lie a),
        h.lieEquiv ((DistribSMul.toLinearMap O (Lie a) r).lTensor M z) = r • h.lieEquiv z) ∧
      ∀ (H' : Over (Sp R)) [GrpObj H'] [IsCommMonObj H'] (b' : OAct O H') (M' : Type)
        [AddCommGroup M'] [Module O M'] (h' : IsTensor H' b' G a M') (φ : M →ₗ[O] M')
        (z : M ⊗[O] Lie a),
        Lie.map b b' (h.mapLeft h' φ) (h.lieEquiv z) = h'.lieEquiv (φ.rTensor _ z)) ∧
    (∀ (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
      (R : Type) [CommRing R] [Algebra (𝓞 K) R] (G H : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
      [GrpObj H] [IsCommMonObj H] (a : OAct (𝓞 K) G) (b : OAct (𝓞 K) H) (M : Type) [AddCommGroup M]
      [Module (𝓞 K) M] [Module (𝓞 E) M] [IsScalarTower (𝓞 K) (𝓞 E) M] (h : IsTensor H b G a M)
      (v : epsR R ⟶ G), IsLieBasis ![v] →
      (∀ x, (v ≫ a.act x).left = spMap (epsScaleR (algebraMap (𝓞 K) R x)) ≫ v.left) →
      ∃ e : R ⊗[𝓞 K] M ≃ₗ[R] Lie (h.algAct (𝓞 E)), (∀ m, (e (1 ⊗ₜ m)).hom = v ≫ h.tmul m) ∧
        ∀ (x : 𝓞 E) (r : R) (m : M), e (r ⊗ₜ (x • m)) = x • e (r ⊗ₜ m)) ∧
    (∀ (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
      (S : Scheme.{0}) (G H : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]
      (a : OAct (𝓞 K) G) (b : OAct (𝓞 K) H) (M : Type) [AddCommGroup M] [Module (𝓞 K) M]
      [Module (𝓞 E) M] [IsScalarTower (𝓞 K) (𝓞 E) M] [Module.Finite (𝓞 E) M]
      [Module.Projective (𝓞 E) M] (h : IsTensor H b G a M) (k : Type) [Field k] [CharZero k]
      (t : Sp k ⟶ S),
      (∀ (τ : 𝓞 E →+* k) (n : ℕ), LieMult a t (τ.comp (algebraMap (𝓞 K) (𝓞 E))) n →
        LieMult (h.algAct (𝓞 E)) t τ (n * Module.finrank (𝓞 E) M)) ∧
      ∀ [IsCMField E] (X : Host E) (D : Datum X) (ρ : k) (r : 𝓞 K) (p₀ q₀ : ℕ),
        algebraMap (𝓞 K) (𝓞 E) r = X.rt →
        (∀ σ : 𝓞 K →+* k, (σ r = ρ → LieMult a t σ p₀) ∧ (σ r ≠ ρ → LieMult a t σ q₀)) →
        D.p = p₀ * Module.finrank (𝓞 E) M → D.q = q₀ * Module.finrank (𝓞 E) M →
        DetCond D (h.algAct (𝓞 E)) t ρ) ∧
    (∀ (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
      (k : Type) [Field k] [CharZero k] (G H : Over (Sp k)) [GrpObj G] [IsCommMonObj G] [GrpObj H]
      [IsCommMonObj H] (a : OAct (𝓞 K) G) (b : OAct (𝓞 K) H)
      (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (h : IsTensor H b G a I) (v : epsR k ⟶ G),
      I ≠ 0 → IsLieBasis ![v] →
      (∀ τ₀ : 𝓞 K →+* k, (∀ x, (v ≫ a.act x).left = spMap (epsScaleR (τ₀ x)) ≫ v.left) →
        ∀ τ : 𝓞 E →+* k,
          (τ.comp (algebraMap (𝓞 K) (𝓞 E)) = τ₀ → LieMult (h.algAct (𝓞 E)) (𝟙 _) τ 1) ∧
          (τ.comp (algebraMap (𝓞 K) (𝓞 E)) ≠ τ₀ → LieMult (h.algAct (𝓞 E)) (𝟙 _) τ 0)) ∧
      ∀ [Algebra K k] [DecidableEq (E →ₐ[K] k)],
        (∀ x : E, ((minpoly K x).map (algebraMap K k)).Splits) →
        (∀ x : 𝓞 K, (v ≫ a.act x).left = spMap (epsScaleR (algebraMap K k x)) ≫ v.left) →
        DirectSum.IsInternal fun σ : E →ₐ[K] k ↦
          Lie.eig (h.algAct (𝓞 E)) ((σ : E →+* k).comp (algebraMap (𝓞 E) E))) := by
  refine ⟨fun R O _ _ G _ _ a ↦ ⟨fun w ↦ ⟨fun hw ↦ ⟨Lie.mk a w hw, rfl⟩, ?_⟩, fun _ _ ↦ Lie.ext,
      Lie.hom_add, Lie.hom_smul_left, Lie.hom_act_smul, smul_comm,
      fun n v ↦ ⟨fun hv ↦ ⟨Lie.basis a hv, Lie.hom_basis hv⟩, ?_⟩,
      fun H K _ _ _ _ b c i f _ _ h ↦ Lie.map_kernel h⟩,
    fun R O _ _ G H _ _ _ _ a b M _ _ h ↦ ⟨h.hom_lieEquiv_tmul, h.lieEquiv_smul,
      fun H' _ _ b' M' _ _ h' ↦ h.mapLeft_lieEquiv h'⟩,
    fun K E _ _ _ _ _ R _ _ G H _ _ _ _ a b M _ _ _ _ h v hv hτ ↦
      ⟨h.lieEquivLine _ hv hτ, fun m ↦ ?_, fun x r m ↦ h.lieEquivLine_smul hv hτ x (r ⊗ₜ m)⟩,
    fun K E _ _ _ _ _ S G H _ _ _ _ a b M _ _ _ _ _ _ h k _ _ t ↦ ⟨fun τ n ↦ h.lieMult t τ,
      fun X D ρ r p₀ q₀ hr ↦ h.detCond D t ρ r hr⟩,
    fun K E _ _ _ _ _ k _ _ G H _ _ _ _ a b I h v hI hv ↦
      ⟨fun τ₀ ↦ h.lieMult_line hI hv, fun hk ↦ h.isInternal_eig hI hk hv⟩⟩
  · rintro ⟨v, rfl⟩
    exact v.isTangent
  · rintro ⟨u, hu⟩
    obtain rfl : (fun i ↦ (u i).hom) = v := funext hu
    exact Lie.isLieBasis_basis u
  · rw [IsTensor.hom_lieEquivLine_tmul, epsScale_one, Category.id_comp]

end GlobalTheory.Serre
