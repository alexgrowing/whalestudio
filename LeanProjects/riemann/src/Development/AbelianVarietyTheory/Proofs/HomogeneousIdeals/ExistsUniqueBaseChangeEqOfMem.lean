import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SpanSingletonEqTopIffIsUnitOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.MemHomogIffIsHomogeneous

open TensorProduct

namespace GlobalTheory

namespace FlatDescent

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {N : Type*} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
  {N' : Type*} [AddCommGroup N'] [Module A N'] [Module B N'] [IsScalarTower A B N']

variable (A B N) in

def act : B ⊗[A] N →ₗ[B] N := LinearMap.liftBaseChange B (LinearMap.id : N →ₗ[A] N)

@[simp] theorem act_tmul (b : B) (n : N) : act A B N (b ⊗ₜ n) = b • n := by
  simp [act]

structure IsDescentDatum (θ : N →ₗ[B] B ⊗[A] N) : Prop where
  counit : ∀ n, act A B N (θ n) = n
  coassoc : ∀ n, (θ.restrictScalars A).lTensor B (θ n) = (TensorProduct.mk A B N 1).lTensor B (θ n)

def invariants (θ : N →ₗ[B] B ⊗[A] N) : Submodule A N :=
  LinearMap.ker (θ.restrictScalars A - TensorProduct.mk A B N 1)

@[simp] theorem mem_invariants {θ : N →ₗ[B] B ⊗[A] N} {n : N} :
    n ∈ invariants θ ↔ θ n = 1 ⊗ₜ n := by
  simp [invariants, sub_eq_zero]

variable (B) in

def canonical (M : Type*) [AddCommGroup M] [Module A M] :
    B ⊗[A] M →ₗ[B] B ⊗[A] (B ⊗[A] M) :=
  (TensorProduct.mk A B M 1).baseChange B

@[simp] theorem canonical_tmul {M : Type*} [AddCommGroup M] [Module A M] (b : B) (m : M) :
    canonical B M (b ⊗ₜ[A] m) = b ⊗ₜ[A] ((1 : B) ⊗ₜ[A] m) := rfl

variable (B) in

theorem isDescentDatum_canonical (M : Type*) [AddCommGroup M] [Module A M] :
    IsDescentDatum (canonical (A := A) B M) := by
  constructor <;> intro x
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b m => simp [smul_tmul']
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b m => simp

variable (B) in

def extend (P : Submodule A N) : B ⊗[A] P →ₗ[B] N := LinearMap.liftBaseChange B P.subtype

@[simp] theorem extend_tmul (P : Submodule A N) (b : B) (n : P) :
    extend B P (b ⊗ₜ n) = b • (n : N) := by
  simp [extend]

theorem act_lTensor_subtype (P : Submodule A N) (x : B ⊗[A] P) :
    act A B N (P.subtype.lTensor B x) = extend B P x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b m => simp

theorem apply_extend (θ : N →ₗ[B] B ⊗[A] N) (x : B ⊗[A] invariants θ) :
    θ (extend B _ x) = (invariants θ).subtype.lTensor B x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b m => simp [mem_invariants.1 m.2, smul_tmul']

theorem apply_extend_eq_canonical (θ : N →ₗ[B] B ⊗[A] N) (x : B ⊗[A] invariants θ) :
    θ (extend B _ x) =
      ((extend B (invariants θ)).restrictScalars A).lTensor B (canonical B _ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b m => simp [mem_invariants.1 m.2, smul_tmul']

theorem IsDescentDatum.bijective_extend [Module.Flat A B] {θ : N →ₗ[B] B ⊗[A] N}
    (h : IsDescentDatum θ) : Function.Bijective (extend B (invariants θ)) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := B) _
      (invariants θ).injective_subtype
    rw [← apply_extend, hx, map_zero, map_zero]
  · intro n
    have hex := Module.Flat.lTensor_exact B
      (LinearMap.exact_subtype_ker_map (θ.restrictScalars A - TensorProduct.mk A B N 1))
    obtain ⟨x, hx⟩ := (hex (θ n)).1 (by
      rw [LinearMap.lTensor_sub, LinearMap.sub_apply, h.coassoc, sub_self])
    exact ⟨x, (act_lTensor_subtype (invariants θ) x).symm.trans
      ((congrArg (act A B N) hx).trans (h.counit n))⟩

theorem IsDescentDatum.isBaseChange [Module.Flat A B] {θ : N →ₗ[B] B ⊗[A] N}
    (h : IsDescentDatum θ) : IsBaseChange B (invariants θ).subtype :=
  IsBaseChange.of_equiv (LinearEquiv.ofBijective _ h.bijective_extend) fun n => by simp

section Amitsur

variable (B) (M : Type*) [AddCommGroup M] [Module A M]

def toInvariants : M →ₗ[A] invariants (canonical (A := A) B M) :=
  (TensorProduct.mk A B M 1).codRestrict _ fun m => by simp

@[simp] theorem coe_toInvariants (m : M) :
    (toInvariants (A := A) B M m : B ⊗[A] M) = 1 ⊗ₜ m := rfl

theorem bijective_toInvariants [Module.FaithfullyFlat A B] :
    Function.Bijective (toInvariants (A := A) B M) := by
  rw [← Module.FaithfullyFlat.lTensor_bijective_iff_bijective A B,
    ← Function.Bijective.of_comp_iff' (isDescentDatum_canonical (A := A) B M).bijective_extend]
  convert Function.bijective_id
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp_all
  | tmul b m => simp [smul_tmul']

def amitsurDiff : B ⊗[A] M →ₗ[A] B ⊗[A] (B ⊗[A] M) :=
  (canonical B M).restrictScalars A - TensorProduct.mk A B (B ⊗[A] M) 1

@[simp] theorem amitsurDiff_tmul (b : B) (m : M) :
    amitsurDiff B M (b ⊗ₜ[A] m) =
      b ⊗ₜ[A] ((1 : B) ⊗ₜ[A] m) - (1 : B) ⊗ₜ[A] (b ⊗ₜ[A] m) := rfl

theorem amitsur_exact [Module.FaithfullyFlat A B] :
    Function.Injective (TensorProduct.mk A B M 1) ∧
      Function.Exact (TensorProduct.mk A B M 1) (amitsurDiff (A := A) B M) := by
  refine ⟨Module.FaithfullyFlat.tensorProduct_mk_injective M, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨m, hm⟩ := (bijective_toInvariants (A := A) B M).2 ⟨x, hx⟩
    exact ⟨m, congrArg Subtype.val hm⟩
  · rintro ⟨m, rfl⟩
    simp

end Amitsur

section Morphisms

def IsCompatible (θ : N →ₗ[B] B ⊗[A] N) (θ' : N' →ₗ[B] B ⊗[A] N') (f : N →ₗ[B] N') : Prop :=
  ∀ n, θ' (f n) = (f.restrictScalars A).lTensor B (θ n)

theorem IsCompatible.map_mem {θ : N →ₗ[B] B ⊗[A] N} {θ' : N' →ₗ[B] B ⊗[A] N'} {f : N →ₗ[B] N'}
    (hf : IsCompatible θ θ' f) {n : N} (hn : n ∈ invariants θ) : f n ∈ invariants θ' := by
  rw [mem_invariants] at hn ⊢
  rw [hf n, hn]
  simp

variable {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']

variable (B) in

theorem isCompatible_baseChange (g : M →ₗ[A] M') :
    IsCompatible (canonical B M) (canonical B M') (g.baseChange B) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b m => simp

theorem existsUnique_baseChange_eq_of_mem [Module.FaithfullyFlat A B]
    (f : B ⊗[A] M →ₗ[B] B ⊗[A] M') (hf : ∀ m : M, f (1 ⊗ₜ m) ∈ invariants (canonical B M')) :
    ∃! g : M →ₗ[A] M', g.baseChange B = f := by
  let e := LinearEquiv.ofBijective _ (bijective_toInvariants (A := A) B M')
  let g : M →ₗ[A] M' := e.symm.toLinearMap ∘ₗ
    ((f.restrictScalars A) ∘ₗ TensorProduct.mk A B M 1).codRestrict _ hf
  have hg : ∀ m, (1 : B) ⊗ₜ[A] g m = f (1 ⊗ₜ m) := fun m =>
    congrArg Subtype.val (e.apply_symm_apply ⟨f (1 ⊗ₜ m), hf m⟩)
  refine ⟨g, ?_, fun g' hg' => ?_⟩
  · ext m
    simpa using hg m
  · ext m
    apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B) M'
    simp only [TensorProduct.mk_apply, hg, ← hg', LinearMap.baseChange_tmul]

theorem IsCompatible.existsUnique_baseChange_eq [Module.FaithfullyFlat A B]
    {f : B ⊗[A] M →ₗ[B] B ⊗[A] M'} (hf : IsCompatible (canonical B M) (canonical B M') f) :
    ∃! g : M →ₗ[A] M', g.baseChange B = f :=
  existsUnique_baseChange_eq_of_mem f fun m => hf.map_mem (by simp)

variable (B) in

theorem bijective_baseChange_iff [Module.FaithfullyFlat A B] (g : M →ₗ[A] M') :
    Function.Bijective (g.baseChange B) ↔ Function.Bijective g :=
  Module.FaithfullyFlat.lTensor_bijective_iff_bijective A B g

end Morphisms

section Invertible

theorem invertible_of_isBaseChange [Module.FaithfullyFlat A B] {M : Type*} [AddCommGroup M]
    [Module A M] {j : M →ₗ[A] N} (hj : IsBaseChange B j) [Module.Invertible B N] :
    Module.Invertible A M := by
  have : Module.Finite A M := Descent.finite_of_isBaseChange hj
  have : Module.Projective A M := Descent.projective_of_isBaseChange hj
  let e : B ⊗[A] (Module.Dual A M ⊗[A] M) ≃ₗ[B] B ⊗[A] A :=
    AlgebraTensorModule.distribBaseChange A B _ _ ≪≫ₗ
      TensorProduct.congr (SymAlg.isBaseChange_dual hj).equiv hj.equiv ≪≫ₗ
        Module.Invertible.linearEquiv B N ≪≫ₗ (AlgebraTensorModule.rid A B B).symm
  have he : (contractLeft A M).baseChange B = e.toLinearMap := by
    ext ξ m
    apply (AlgebraTensorModule.rid A B B).injective
    simp [e, Module.Invertible.linearEquiv, hj.toDual_comp_apply, Algebra.algebraMap_eq_smul_one]
  refine ⟨(bijective_baseChange_iff B _).1 ?_⟩
  rw [he]
  exact e.bijective

variable (B) in

theorem invertible_baseChange_iff [Module.FaithfullyFlat A B] (M : Type*) [AddCommGroup M]
    [Module A M] : Module.Invertible B (B ⊗[A] M) ↔ Module.Invertible A M :=
  ⟨fun _ => invertible_of_isBaseChange (TensorProduct.isBaseChange A M B), fun _ => inferInstance⟩

theorem IsDescentDatum.invertible_invariants [Module.FaithfullyFlat A B]
    {θ : N →ₗ[B] B ⊗[A] N} (h : IsDescentDatum θ) [Module.Invertible B N] :
    Module.Invertible A (invariants θ) :=
  invertible_of_isBaseChange h.isBaseChange

variable (B) in

theorem isUnit_algebraMap_iff [Module.FaithfullyFlat A B] (a : A) :
    IsUnit (algebraMap A B a) ↔ IsUnit a := by
  rw [isUnit_iff_dvd_one, isUnit_iff_dvd_one, ← Descent.algebraMap_dvd_iff B a 1, map_one]

end Invertible

section Gluing

variable (A) in

def smulRight (b : B) : B ⊗[A] N →ₗ[B] B ⊗[A] N :=
  (Algebra.lsmul A A N b).baseChange B

@[simp] theorem smulRight_tmul (b c : B) (n : N) :
    smulRight A b (c ⊗ₜ[A] n) = c ⊗ₜ[A] (b • n) := rfl

structure IsGluing (φ : N ⊗[A] B →ₗ[B] B ⊗[A] N) : Prop where
  bijective : Function.Bijective φ
  map_tmul_mul : ∀ (n : N) (b c : B), φ (n ⊗ₜ (b * c)) = smulRight A b (φ (n ⊗ₜ c))
  cocycle : ∀ (n : N) (b c : B),
    (φ.restrictScalars A).lTensor B (TensorProduct.assoc A B N B (φ (n ⊗ₜ b) ⊗ₜ c)) =
      (TensorProduct.mk A B N b).lTensor B (φ (n ⊗ₜ c))

def datumOfGluing (φ : N ⊗[A] B →ₗ[B] B ⊗[A] N) : N →ₗ[B] B ⊗[A] N :=
  φ ∘ₗ (AlgebraTensorModule.mk A B N B).flip 1

@[simp] theorem datumOfGluing_apply (φ : N ⊗[A] B →ₗ[B] B ⊗[A] N) (n : N) :
    datumOfGluing φ n = φ (n ⊗ₜ 1) := rfl

def gluingOfDatum (θ : N →ₗ[B] B ⊗[A] N) : N ⊗[A] B →ₗ[B] B ⊗[A] N :=
  AlgebraTensorModule.lift
    { toFun := fun n =>
        { toFun := fun b => smulRight A b (θ n)
          map_add' := fun b c => by
            induction θ n using TensorProduct.induction_on with
            | zero => simp
            | add x y hx hy => simp only [map_add, hx, hy]; abel
            | tmul b m => simp [add_smul, tmul_add]
          map_smul' := fun a b => by
            induction θ n using TensorProduct.induction_on with
            | zero => simp
            | add x y hx hy => simp only [map_add, hx, hy, smul_add]
            | tmul b m => simp }
      map_add' := fun n n' => by ext; simp
      map_smul' := fun b n => by ext; simp }

@[simp] theorem gluingOfDatum_tmul (θ : N →ₗ[B] B ⊗[A] N) (n : N) (b : B) :
    gluingOfDatum θ (n ⊗ₜ b) = smulRight A b (θ n) := rfl

theorem smulRight_one (x : B ⊗[A] N) : smulRight A (1 : B) x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b m => simp

theorem smulRight_mul (b c : B) (x : B ⊗[A] N) :
    smulRight A (b * c) x = smulRight A b (smulRight A c x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b m => simp [mul_smul]

theorem IsGluing.isDescentDatum {φ : N ⊗[A] B →ₗ[B] B ⊗[A] N} (h : IsGluing φ) :
    IsDescentDatum (datumOfGluing φ) := by
  have hco : ∀ n, ((datumOfGluing φ).restrictScalars A).lTensor B (datumOfGluing φ n) =
      (TensorProduct.mk A B N 1).lTensor B (datumOfGluing φ n) := by
    intro n
    rw [datumOfGluing_apply, ← h.cocycle]
    induction φ (n ⊗ₜ 1) using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, add_tmul]
    | tmul b m => simp
  refine ⟨fun n => ?_, hco⟩
  have h1 : ∀ x : B ⊗[A] N, act A B _ (((datumOfGluing φ).restrictScalars A).lTensor B x) =
      datumOfGluing φ (act A B N x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b m => simp [← smul_tmul']
  have h2 : ∀ x : B ⊗[A] N, act A B _ ((TensorProduct.mk A B N 1).lTensor B x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b m => simp [smul_tmul']
  have h3 := congrArg (act A B _) (hco n)
  rw [h1, h2] at h3
  have h4 := congrArg (fun x => act A B N (TensorProduct.comm A N B x)) (h.bijective.1 h3)
  simpa using h4

theorem IsDescentDatum.isGluing {θ : N →ₗ[B] B ⊗[A] N} (h : IsDescentDatum θ) :
    IsGluing (gluingOfDatum θ) := by
  let φ : N ⊗[A] B →ₗ[A] B ⊗[A] N := (gluingOfDatum θ).restrictScalars A
  let τ := TensorProduct.comm A B N
  let κ : B ⊗[A] (B ⊗[A] N) →ₗ[A] B ⊗[A] N :=
    ((act A B N).restrictScalars A).lTensor B ∘ₗ (TensorProduct.leftComm A B B N).toLinearMap
  have hκ : ∀ (b : B) (x : B ⊗[A] N), κ (b ⊗ₜ x) = smulRight A b x := by
    intro b x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, tmul_add]
    | tmul b m => simp [κ]
  have h1 : ∀ (b : B) (x : B ⊗[A] N),
      φ (τ (smulRight A b x)) = b • κ ((θ.restrictScalars A).lTensor B x) := by
    intro b x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
    | tmul c m => simp [hκ, φ, τ]
  have h2 : ∀ x : B ⊗[A] N, κ ((TensorProduct.mk A B N 1).lTensor B x) = 1 ⊗ₜ act A B N x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, tmul_add]
    | tmul c m => simp [hκ]
  have h3 : ∀ x, τ (φ (τ (φ x))) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul n b =>
      have : φ (n ⊗ₜ b) = smulRight A b (θ n) := rfl
      rw [this, h1, h.coassoc, h2, h.counit]
      simp [τ, smul_tmul']
  refine ⟨⟨fun x y hxy => ?_, fun y => ⟨τ (φ (τ y)), ?_⟩⟩, fun n b c => ?_, fun n b c => ?_⟩
  · rw [← h3 x, ← h3 y]
    exact congrArg (fun z => τ (φ (τ z))) hxy
  · obtain ⟨y, rfl⟩ := τ.symm.surjective y
    have hτφ : Function.Bijective (fun x => τ (φ x)) := Function.Involutive.bijective h3
    obtain ⟨z, rfl⟩ := hτφ.2 y
    simp only [LinearEquiv.symm_apply_apply]
    rw [h3]
    rfl
  · simp [smulRight_mul]
  · let ψ : B ⊗[A] N →ₗ[A] B ⊗[A] N := (b • smulRight A c : B ⊗[A] N →ₗ[B] B ⊗[A] N).restrictScalars A
    have h4 : ∀ x : B ⊗[A] N, φ.lTensor B (TensorProduct.assoc A B N B (smulRight A b x ⊗ₜ c)) =
        ψ.lTensor B ((θ.restrictScalars A).lTensor B x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy, add_tmul]
      | tmul d m => simp [φ, ψ]
    have h5 : ∀ x : B ⊗[A] N, ψ.lTensor B ((TensorProduct.mk A B N 1).lTensor B x) =
        (TensorProduct.mk A B N b).lTensor B (smulRight A c x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul d m => simp [ψ, smul_tmul']
    rw [gluingOfDatum_tmul, gluingOfDatum_tmul, ← h5, ← h.coassoc, ← h4]

variable (A B N) in

def gluingEquivDatum : {φ : N ⊗[A] B →ₗ[B] B ⊗[A] N // IsGluing φ} ≃
    {θ : N →ₗ[B] B ⊗[A] N // IsDescentDatum θ} where
  toFun φ := ⟨datumOfGluing φ.1, φ.2.isDescentDatum⟩
  invFun θ := ⟨gluingOfDatum θ.1, θ.2.isGluing⟩
  left_inv φ := by
    ext n b
    simp [← φ.2.map_tmul_mul]
  right_inv θ := by
    ext n
    simp [smulRight_one]

end Gluing

end FlatDescent

end GlobalTheory
