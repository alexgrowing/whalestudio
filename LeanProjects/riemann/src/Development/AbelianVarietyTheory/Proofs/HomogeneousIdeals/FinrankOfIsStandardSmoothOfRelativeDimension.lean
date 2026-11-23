import Mathlib

open TensorProduct

noncomputable section

namespace GlobalTheory

abbrev AugCot {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (ε : A →ₐ[R] R) : Type _ :=
  (RingHom.ker ε).Cotangent

namespace AugCot

section Basic

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (ε : A →ₐ[R] R)

def projKer : A →ₗ[R] RingHom.ker ε :=
  LinearMap.codRestrict ((RingHom.ker ε).restrictScalars R)
    (LinearMap.id - (Algebra.linearMap R A) ∘ₗ ε.toLinearMap)
    (fun a => by simp [RingHom.mem_ker])

@[simp] lemma coe_projKer (a : A) : (projKer ε a : A) = a - algebraMap R A (ε a) := rfl

@[simp] lemma projKer_coe (x : RingHom.ker ε) : projKer ε x = x := by
  have hx : ε x = 0 := x.2
  ext; simp [hx]

def d : A →ₗ[R] AugCot ε :=
  ((RingHom.ker ε).toCotangent.restrictScalars R) ∘ₗ projKer ε

lemma d_apply (a : A) : d ε a = (RingHom.ker ε).toCotangent (projKer ε a) := rfl

@[simp] lemma d_coe (x : RingHom.ker ε) : d ε x = (RingHom.ker ε).toCotangent x := by
  rw [d_apply, projKer_coe]

lemma d_of_mem {a : A} (ha : a ∈ RingHom.ker ε) :
    d ε a = (RingHom.ker ε).toCotangent ⟨a, ha⟩ := d_coe ε ⟨a, ha⟩

lemma d_surjective : Function.Surjective (d ε) := by
  intro x
  obtain ⟨x, rfl⟩ := (RingHom.ker ε).toCotangent_surjective x
  exact ⟨x, d_coe ε x⟩

lemma d_eq_zero_iff (a : A) : d ε a = 0 ↔ a - algebraMap R A (ε a) ∈ RingHom.ker ε ^ 2 := by
  rw [d_apply, Ideal.toCotangent_eq_zero, coe_projKer]

@[simp] lemma d_algebraMap (r : R) : d ε (algebraMap R A r) = 0 := by
  simp [d_eq_zero_iff]

@[simp] lemma d_one : d ε 1 = 0 := by
  simp [d_eq_zero_iff]

lemma smul_eq (a : A) (x : AugCot ε) : a • x = ε a • x := by
  have h := Ideal.Cotangent.smul_eq_zero_of_mem (projKer ε a).2 x
  rw [coe_projKer, sub_smul, algebraMap_smul, sub_eq_zero] at h
  exact h

lemma d_mul (a b : A) : d ε (a * b) = ε a • d ε b + ε b • d ε a := by
  rw [← smul_eq, ← smul_eq, d_apply, d_apply, d_apply, ← LinearMap.map_smul (RingHom.ker ε).toCotangent,
    ← LinearMap.map_smul (RingHom.ker ε).toCotangent, ← map_add,
    Ideal.toCotangent_eq]
  have : ((projKer ε (a * b) : A) - ((a • projKer ε b + b • projKer ε a : RingHom.ker ε) : A))
      = -((projKer ε a : A) * (projKer ε b : A)) := by
    simp only [coe_projKer, map_mul, Submodule.coe_add, SetLike.val_smul, smul_eq_mul]
    ring
  rw [this, pow_two]
  exact neg_mem (Ideal.mul_mem_mul (projKer ε a).2 (projKer ε b).2)

variable {N : Type*} [AddCommGroup N] [Module R N]

variable {ε} in

lemma hom_ext {f g : AugCot ε →ₗ[R] N} (h : ∀ a, f (d ε a) = g (d ε a)) : f = g := by
  ext x
  obtain ⟨a, rfl⟩ := d_surjective ε x
  exact h a

variable (N) in

def pointDer : Submodule R (A →ₗ[R] N) where
  carrier := {D | ∀ a b, D (a * b) = ε a • D b + ε b • D a}
  add_mem' {D E} hD hE a b := by
    simp only [LinearMap.add_apply, hD a b, hE a b, smul_add]; abel
  zero_mem' a b := by simp
  smul_mem' c D hD a b := by
    simp only [LinearMap.smul_apply, hD a b, smul_add, smul_comm c]

variable {ε} in
lemma mem_pointDer {D : A →ₗ[R] N} :
    D ∈ pointDer ε N ↔ ∀ a b, D (a * b) = ε a • D b + ε b • D a := Iff.rfl

variable {ε} in
lemma pointDer_algebraMap {D : A →ₗ[R] N} (hD : ∀ a b, D (a * b) = ε a • D b + ε b • D a)
    (r : R) : D (algebraMap R A r) = 0 := by
  have h1 : D 1 = 0 := by
    have := hD 1 1
    simpa using this
  rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]

def lift (D : A →ₗ[R] N) (hD : ∀ a b, D (a * b) = ε a • D b + ε b • D a) : AugCot ε →ₗ[R] N :=
  Ideal.Cotangent.lift (D ∘ₗ (RingHom.ker ε).subtype.restrictScalars R) (fun x y => by
    have hx : ε x = 0 := x.2
    have hy : ε y = 0 := y.2
    change D ((x : A) * (y : A)) = 0
    rw [hD, hx, hy, zero_smul, zero_smul, add_zero])

@[simp] lemma lift_toCotangent (D : A →ₗ[R] N) (hD : ∀ a b, D (a * b) = ε a • D b + ε b • D a)
    (x : RingHom.ker ε) : lift ε D hD ((RingHom.ker ε).toCotangent x) = D x := rfl

@[simp] lemma lift_d (D : A →ₗ[R] N) (hD : ∀ a b, D (a * b) = ε a • D b + ε b • D a) (a : A) :
    lift ε D hD (d ε a) = D a := by
  rw [d_apply, lift_toCotangent, coe_projKer, map_sub, pointDer_algebraMap hD, sub_zero]

variable (N) in

def pointDerEquiv : pointDer ε N ≃ₗ[R] (AugCot ε →ₗ[R] N) where
  toFun D := lift ε D.1 (mem_pointDer.1 D.2)
  map_add' D E := hom_ext fun a => by simp
  map_smul' c D := hom_ext fun a => by simp
  invFun f := ⟨f ∘ₗ d ε, fun a b => by simp [d_mul]⟩
  left_inv D := by ext a; simp
  right_inv f := hom_ext fun a => by simp

@[simp] lemma pointDerEquiv_d (D : pointDer ε N) (a : A) :
    pointDerEquiv ε N D (d ε a) = D.1 a := lift_d ε D.1 D.2 a

@[simp] lemma pointDerEquiv_symm_apply (f : AugCot ε →ₗ[R] N) (a : A) :
    ((pointDerEquiv ε N).symm f).1 a = f (d ε a) := rfl

def derivationEquiv [Module A N] [IsScalarTower R A N] (h : ∀ (a : A) (n : N), a • n = ε a • n) :
    Derivation R A N ≃ₗ[R] (AugCot ε →ₗ[R] N) where
  toFun D := lift ε D.toLinearMap (fun a b => by simp [h])
  map_add' D E := hom_ext fun a => by simp
  map_smul' c D := hom_ext fun a => by simp
  invFun f := Derivation.mk' (f ∘ₗ d ε) (fun a b => by simp [d_mul, h])
  left_inv D := by ext a; simp
  right_inv f := hom_ext fun a => by simp

@[simp] lemma derivationEquiv_d [Module A N] [IsScalarTower R A N]
    (h : ∀ (a : A) (n : N), a • n = ε a • n) (D : Derivation R A N) (a : A) :
    derivationEquiv ε h D (d ε a) = D a := lift_d ε D.toLinearMap (fun a b => by simp [h]) a

@[simp] lemma derivationEquiv_symm_apply [Module A N] [IsScalarTower R A N]
    (h : ∀ (a : A) (n : N), a • n = ε a • n) (f : AugCot ε →ₗ[R] N) (a : A) :
    (derivationEquiv ε h).symm f a = f (d ε a) := rfl

lemma isScalarTower_of_smul_eq [Module A N] (h : ∀ (a : A) (n : N), a • n = ε a • n) :
    IsScalarTower R A N :=
  ⟨fun r a n => by rw [h, h, map_smul, smul_assoc]⟩

def derivation : Derivation R A (AugCot ε) :=
  Derivation.mk' (d ε) (fun a b => by rw [d_mul, smul_eq, smul_eq])

@[simp] lemma derivation_apply (a : A) : derivation ε a = d ε a := rfl

section Kaehler

variable [Algebra A R] (h : ∀ a, algebraMap A R a = ε a)

include h in
lemma isScalarTower_of_algebraMap_eq : IsScalarTower A R (AugCot ε) :=
  ⟨fun a r x => by rw [Algebra.smul_def, mul_smul, h, smul_eq]⟩

include h in
lemma isScalarTower_base : IsScalarTower R A R :=
  IsScalarTower.of_algebraMap_eq fun r => by simp [h]

def toKaehler : AugCot ε →ₗ[R] R ⊗[A] Ω[A⁄R] :=
  haveI := isScalarTower_base ε h
  lift ε ((TensorProduct.mk A R Ω[A⁄R] 1).restrictScalars R ∘ₗ
    (KaehlerDifferential.D R A).toLinearMap) (fun a b => by
      simp [tmul_add, tmul_smul, smul_tmul', Algebra.smul_def, h])

@[simp] lemma toKaehler_d (a : A) :
    toKaehler ε h (d ε a) = 1 ⊗ₜ KaehlerDifferential.D R A a := lift_d ε _ _ a

def ofKaehler : Ω[A⁄R] →ₗ[A] AugCot ε := (derivation ε).liftKaehlerDifferential

omit [Algebra A R] in
@[simp] lemma ofKaehler_D (a : A) : ofKaehler ε (KaehlerDifferential.D R A a) = d ε a :=
  Derivation.liftKaehlerDifferential_comp_D _ a

lemma toKaehler_ofKaehler (m : Ω[A⁄R]) : toKaehler ε h (ofKaehler ε m) = 1 ⊗ₜ m := by
  have hm : m ∈ Submodule.span A (Set.range (KaehlerDifferential.D R A)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hm using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; simp
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, tmul_add]
  | smul a x _ hx =>
    rw [map_smul, smul_eq, map_smul, hx, tmul_smul, smul_tmul', smul_tmul', Algebra.smul_def,
      Algebra.smul_def a, h]
    simp

def kaehlerEquiv : AugCot ε ≃ₗ[R] R ⊗[A] Ω[A⁄R] :=
  haveI := isScalarTower_of_algebraMap_eq ε h
  LinearEquiv.ofLinear (toKaehler ε h) (LinearMap.liftBaseChange R (ofKaehler ε))
    (by
      refine LinearMap.ext fun x => ?_
      induction x with
      | zero => simp
      | add x y hx hy => rw [map_add, hx, hy, map_add]
      | tmul r m => simp [toKaehler_ofKaehler, smul_tmul'])
    (hom_ext fun a => by simp)

@[simp] lemma kaehlerEquiv_d (a : A) :
    kaehlerEquiv ε h (d ε a) = 1 ⊗ₜ KaehlerDifferential.D R A a := toKaehler_d ε h a

@[simp] lemma kaehlerEquiv_symm_tmul (r : R) (m : Ω[A⁄R]) :
    (kaehlerEquiv ε h).symm (r ⊗ₜ m) = r • ofKaehler ε m := by
  rw [LinearEquiv.symm_apply_eq, map_smul]
  change _ = r • toKaehler ε h _
  rw [toKaehler_ofKaehler, smul_tmul', smul_eq_mul, mul_one]

lemma isBaseChange_ofKaehler :
    haveI := isScalarTower_of_algebraMap_eq ε h
    IsBaseChange R (ofKaehler ε) :=
  haveI := isScalarTower_of_algebraMap_eq ε h
  IsBaseChange.of_equiv (kaehlerEquiv ε h).symm (fun m => by simp)

end Kaehler

section SqZero

variable [Module Rᵐᵒᵖ N] [IsCentralScalar R N]

def toSqZero (f : AugCot ε →ₗ[R] N) : A →ₐ[R] TrivSqZeroExt R N :=
  AlgHom.ofLinearMap
    ((TrivSqZeroExt.inlAlgHom R R N).toLinearMap ∘ₗ ε.toLinearMap +
      TrivSqZeroExt.inrHom R N ∘ₗ f ∘ₗ d ε)
    (by ext <;> simp)
    (fun a b => by ext <;> simp [d_mul])

@[simp] lemma fst_toSqZero (f : AugCot ε →ₗ[R] N) (a : A) : (toSqZero ε f a).fst = ε a := by
  simp [toSqZero]

@[simp] lemma snd_toSqZero (f : AugCot ε →ₗ[R] N) (a : A) :
    (toSqZero ε f a).snd = f (d ε a) := by
  simp [toSqZero]

def ofSqZero (φ : A →ₐ[R] TrivSqZeroExt R N) (hφ : ∀ a, (φ a).fst = ε a) : AugCot ε →ₗ[R] N :=
  lift ε (TrivSqZeroExt.sndHom R N ∘ₗ φ.toLinearMap) (fun a b => by simp [hφ])

@[simp] lemma ofSqZero_d (φ : A →ₐ[R] TrivSqZeroExt R N) (hφ : ∀ a, (φ a).fst = ε a) (a : A) :
    ofSqZero ε φ hφ (d ε a) = (φ a).snd := lift_d ε _ _ a

variable (N) in

def sqZeroEquiv :
    {φ : A →ₐ[R] TrivSqZeroExt R N // (TrivSqZeroExt.fstHom R R N).comp φ = ε} ≃
      (AugCot ε →ₗ[R] N) where
  toFun φ := ofSqZero ε φ.1 (fun a => AlgHom.congr_fun φ.2 a)
  invFun f := ⟨toSqZero ε f, by ext a; simp⟩
  left_inv φ := by
    have : ∀ a, (φ.1 a).fst = ε a := fun a => AlgHom.congr_fun φ.2 a
    ext a
    · simp [this]
    · exact (snd_toSqZero ε _ a).trans (ofSqZero_d ε _ this a)
  right_inv f := hom_ext fun a =>
    (ofSqZero_d ε _ (fst_toSqZero ε f) a).trans (snd_toSqZero ε f a)

@[simp] lemma sqZeroEquiv_d
    (φ : {φ : A →ₐ[R] TrivSqZeroExt R N // (TrivSqZeroExt.fstHom R R N).comp φ = ε}) (a : A) :
    sqZeroEquiv ε N φ (d ε a) = (φ.1 a).snd :=
  ofSqZero_d ε φ.1 (fun a => AlgHom.congr_fun φ.2 a) a

@[simp] lemma sqZeroEquiv_symm_apply (f : AugCot ε →ₗ[R] N) :
    ((sqZeroEquiv ε N).symm f).1 = toSqZero ε f := rfl

end SqZero

end Basic

section Map

variable {R A B C : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  [CommRing C] [Algebra R C] {εA : A →ₐ[R] R} {εB : B →ₐ[R] R} {εC : C →ₐ[R] R}

lemma ker_eq_comap (φ : A →ₐ[R] B) (h : εB.comp φ = εA) :
    RingHom.ker εA = (RingHom.ker εB).comap φ := by
  subst h; ext a; simp [RingHom.mem_ker]

def map (φ : A →ₐ[R] B) (h : εB.comp φ = εA) : AugCot εA →ₗ[R] AugCot εB :=
  Ideal.mapCotangent _ _ φ (ker_eq_comap φ h).le

@[simp] lemma map_toCotangent (φ : A →ₐ[R] B) (h : εB.comp φ = εA) (x : RingHom.ker εA) :
    map φ h ((RingHom.ker εA).toCotangent x) =
      (RingHom.ker εB).toCotangent ⟨φ x, (ker_eq_comap φ h).le x.2⟩ := rfl

@[simp] lemma map_d (φ : A →ₐ[R] B) (h : εB.comp φ = εA) (a : A) :
    map φ h (d εA a) = d εB (φ a) := by
  rw [d_apply, d_apply, map_toCotangent]
  congr 1
  ext
  simp [← h]

@[simp] lemma map_id : map (AlgHom.id R A) (AlgHom.comp_id εA) = LinearMap.id :=
  hom_ext fun a => by simp

lemma map_comp (φ : A →ₐ[R] B) (ψ : B →ₐ[R] C) (h : εB.comp φ = εA) (h' : εC.comp ψ = εB)
    (h'' : εC.comp (ψ.comp φ) = εA := by rw [← AlgHom.comp_assoc, h', h]) :
    map (ψ.comp φ) h'' = map ψ h' ∘ₗ map φ h :=
  hom_ext fun a => by simp

def congr (e : A ≃ₐ[R] B) (h : εB.comp e = εA) : AugCot εA ≃ₗ[R] AugCot εB :=
  LinearEquiv.ofLinear (map (e : A →ₐ[R] B) h)
    (map (e.symm : B →ₐ[R] A) (by subst h; ext b; simp))
    (hom_ext fun a => by simp) (hom_ext fun a => by simp)

@[simp] lemma congr_d (e : A ≃ₐ[R] B) (h : εB.comp e = εA) (a : A) :
    congr e h (d εA a) = d εB (e a) := map_d (e : A →ₐ[R] B) h a

@[simp] lemma congr_symm_d (e : A ≃ₐ[R] B) (h : εB.comp e = εA) (b : B) :
    (congr e h).symm (d εB b) = d εA (e.symm b) := by
  rw [LinearEquiv.symm_apply_eq, congr_d, e.apply_symm_apply]

lemma map_ofKaehler [Algebra A B] [IsScalarTower R A B]
    (h : εB.comp (IsScalarTower.toAlgHom R A B) = εA) (m : Ω[A⁄R]) :
    map _ h (ofKaehler εA m) = ofKaehler εB (KaehlerDifferential.map R R A B m) := by
  have hm : m ∈ Submodule.span A (Set.range (KaehlerDifferential.D R A)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hm using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; simp [KaehlerDifferential.map_D]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
    rw [map_smul, smul_eq, map_smul, hx, map_smul, ← algebraMap_smul B a, map_smul, smul_eq, ← h]
    rfl

lemma map_surjective (φ : A →ₐ[R] B) (h : εB.comp φ = εA) (hφ : Function.Surjective φ) :
    Function.Surjective (map φ h) := by
  intro x
  obtain ⟨b, rfl⟩ := d_surjective εB x
  obtain ⟨a, rfl⟩ := hφ b
  exact ⟨d εA a, map_d φ h a⟩

lemma ker_le (φ : A →ₐ[R] B) (h : εB.comp φ = εA) : RingHom.ker φ ≤ RingHom.ker εA := by
  intro a ha
  rw [RingHom.mem_ker] at ha ⊢
  rw [← h, AlgHom.comp_apply, ha, map_zero]

def kerMap (φ : A →ₐ[R] B) (h : εB.comp φ = εA) : RingHom.ker φ →ₗ[R] AugCot εA :=
  ((RingHom.ker εA).toCotangent ∘ₗ Submodule.inclusion (ker_le φ h)).restrictScalars R

@[simp] lemma kerMap_apply (φ : A →ₐ[R] B) (h : εB.comp φ = εA) (x : RingHom.ker φ) :
    kerMap φ h x = d εA x := (d_of_mem εA (ker_le φ h x.2)).symm

lemma exact_kerMap_map (φ : A →ₐ[R] B) (h : εB.comp φ = εA) (hφ : Function.Surjective φ) :
    Function.Exact (kerMap φ h) (map φ h) := by
  intro x
  constructor
  · intro hx
    obtain ⟨x, rfl⟩ := (RingHom.ker εA).toCotangent_surjective x
    rw [map_toCotangent, Ideal.toCotangent_eq_zero] at hx
    have hI : RingHom.ker εB = (RingHom.ker εA).map φ := by
      rw [ker_eq_comap φ h, Ideal.map_comap_of_surjective _ hφ]
    have hx' : φ x ∈ (RingHom.ker εA ^ 2).map φ := by
      rw [Ideal.map_pow, ← hI]; exact hx
    obtain ⟨y, hy, hxy⟩ := (Ideal.mem_map_iff_of_surjective _ hφ).1 hx'
    refine ⟨⟨x - y, by simp [RingHom.mem_ker, hxy]⟩, ?_⟩
    have hy' : y ∈ RingHom.ker εA := Ideal.pow_le_self two_ne_zero hy
    have : d εA y = 0 := by rw [d_of_mem εA hy', Ideal.toCotangent_eq_zero]; exact hy
    simp [this]
  · rintro ⟨x, rfl⟩
    have : φ x = 0 := x.2
    simp [this]

lemma isNilpotent_ker_fst (N : Type*) [AddCommGroup N] [Module R N] [Module Rᵐᵒᵖ N]
    [IsCentralScalar R N] :
    IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom R R N : TrivSqZeroExt R N →+* R)) := by
  refine ⟨2, ?_⟩
  rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  have hx : x.fst = 0 := hx
  have hy : y.fst = 0 := hy
  rw [Ideal.mem_bot]
  ext <;> simp [hx, hy]

lemma exists_leftInverse_map (φ : A →ₐ[R] B) (h : εB.comp φ = εA)
    (hφ : (φ : A →+* B).FormallySmooth) :
    ∃ s : AugCot εB →ₗ[R] AugCot εA, s ∘ₗ map φ h = LinearMap.id := by
  letI : Module Rᵐᵒᵖ (AugCot εA) :=
    Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  haveI : IsCentralScalar R (AugCot εA) := ⟨fun _ _ => rfl⟩
  letI : Algebra A B := (φ : A →+* B).toAlgebra
  haveI : Algebra.FormallySmooth A B := hφ
  letI : Algebra A R := (εA : A →+* R).toAlgebra
  let ψ := toSqZero εA (LinearMap.id (M := AugCot εA))
  letI : Algebra A (TrivSqZeroExt R (AugCot εA)) := (ψ : A →+* _).toAlgebra
  let f : B →ₐ[A] R := { (εB : B →+* R) with commutes' := fun a => AlgHom.congr_fun h a }
  let g : TrivSqZeroExt R (AugCot εA) →ₐ[A] R :=
    { (TrivSqZeroExt.fstHom R R (AugCot εA) : TrivSqZeroExt R (AugCot εA) →+* R) with
      commutes' := fun a => fst_toSqZero εA _ a }
  have hg : Function.Surjective g := fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
  let l := Algebra.FormallySmooth.liftOfSurjective f g hg (isNilpotent_ker_fst _)
  have hl : ∀ a, l (φ a) = ψ a := fun a => l.commutes a
  let l' : B →ₐ[R] TrivSqZeroExt R (AugCot εA) :=
    { (l : B →+* TrivSqZeroExt R (AugCot εA)) with
      commutes' := fun r => by
        have := hl (algebraMap R A r)
        rw [φ.commutes, ψ.commutes] at this
        exact this }
  have hl' : ∀ b, (l' b).fst = εB b := fun b =>
    Algebra.FormallySmooth.liftOfSurjective_apply f g hg (isNilpotent_ker_fst _) b
  refine ⟨ofSqZero εB l' hl', hom_ext fun a => ?_⟩
  rw [LinearMap.comp_apply, map_d, ofSqZero_d]
  exact (congrArg TrivSqZeroExt.snd (hl a)).trans (snd_toSqZero εA _ a)

lemma map_injective_of_formallySmooth (φ : A →ₐ[R] B) (h : εB.comp φ = εA)
    (hφ : (φ : A →+* B).FormallySmooth) : Function.Injective (map φ h) := by
  obtain ⟨s, hs⟩ := exists_leftInverse_map φ h hφ
  exact Function.LeftInverse.injective (g := s) (LinearMap.congr_fun hs)

lemma map_surjective_of_formallyUnramified (φ : A →ₐ[R] B) (h : εB.comp φ = εA)
    (hφ : (φ : A →+* B).FormallyUnramified) : Function.Surjective (map φ h) := by
  let N := AugCot εB ⧸ LinearMap.range (map φ h)
  letI : Module Rᵐᵒᵖ N := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  haveI : IsCentralScalar R N := ⟨fun _ _ => rfl⟩
  letI : Algebra A B := (φ : A →+* B).toAlgebra
  haveI : Algebra.FormallyUnramified A B := hφ
  let q : AugCot εB →ₗ[R] N := (LinearMap.range (map φ h)).mkQ
  let ψ := toSqZero εA (0 : AugCot εA →ₗ[R] N)
  letI : Algebra A (TrivSqZeroExt R N) := (ψ : A →+* _).toAlgebra
  have hε : ∀ a, εB (φ a) = εA a := fun a => AlgHom.congr_fun h a
  let g₁ : B →ₐ[A] TrivSqZeroExt R N :=
    { (toSqZero εB q : B →+* TrivSqZeroExt R N) with
      commutes' := fun a => by
        change toSqZero εB q (φ a) = ψ a
        ext
        · simp [ψ, hε]
        · simp only [ψ, snd_toSqZero, LinearMap.zero_apply, ← map_d φ h]
          exact (Submodule.Quotient.mk_eq_zero _).2 ⟨_, rfl⟩ }
  let g₂ : B →ₐ[A] TrivSqZeroExt R N :=
    { (toSqZero εB (0 : AugCot εB →ₗ[R] N) : B →+* TrivSqZeroExt R N) with
      commutes' := fun a => by
        change toSqZero εB 0 (φ a) = ψ a
        ext <;> simp [ψ, hε] }
  have := Algebra.FormallyUnramified.ext'
    (TrivSqZeroExt.fstHom R R N : TrivSqZeroExt R N →+* R) (isNilpotent_ker_fst _) g₁ g₂
    (fun b => (fst_toSqZero εB q b).trans (fst_toSqZero εB 0 b).symm)
  intro x
  obtain ⟨b, rfl⟩ := d_surjective εB x
  have hb : toSqZero εB q b = toSqZero εB (0 : AugCot εB →ₗ[R] N) b := AlgHom.congr_fun this b
  have hb' := congrArg TrivSqZeroExt.snd hb
  rw [snd_toSqZero, snd_toSqZero, LinearMap.zero_apply] at hb'
  exact (Submodule.Quotient.mk_eq_zero _).1 hb'

lemma map_bijective_of_formallyEtale (φ : A →ₐ[R] B) (h : εB.comp φ = εA)
    (hφ : (φ : A →+* B).FormallyEtale) : Function.Bijective (map φ h) := by
  letI : Algebra A B := (φ : A →+* B).toAlgebra
  haveI : Algebra.FormallyEtale A B := hφ
  exact ⟨map_injective_of_formallySmooth φ h (inferInstanceAs (Algebra.FormallySmooth A B)),
    map_surjective_of_formallyUnramified φ h
      (inferInstanceAs (Algebra.FormallyUnramified A B))⟩

lemma map_bijective_of_etale (φ : A →ₐ[R] B) (h : εB.comp φ = εA)
    (hφ : (φ : A →+* B).Etale) : Function.Bijective (map φ h) := by
  letI : Algebra A B := (φ : A →+* B).toAlgebra
  haveI : Algebra.Etale A B := hφ
  exact map_bijective_of_formallyEtale φ h (inferInstanceAs (Algebra.FormallyEtale A B))

section Tower

variable [Algebra A B] [IsScalarTower R A B]

lemma map_bijective [Algebra.FormallyEtale A B]
    (h : εB.comp (IsScalarTower.toAlgHom R A B) = εA) : Function.Bijective (map _ h) :=
  map_bijective_of_formallyEtale _ h (RingHom.formallyEtale_algebraMap.2 inferInstance)

def etaleEquiv [Algebra.FormallyEtale A B] (h : εB.comp (IsScalarTower.toAlgHom R A B) = εA) :
    AugCot εA ≃ₗ[R] AugCot εB := LinearEquiv.ofBijective (map _ h) (map_bijective h)

@[simp] lemma etaleEquiv_d [Algebra.FormallyEtale A B]
    (h : εB.comp (IsScalarTower.toAlgHom R A B) = εA) (a : A) :
    etaleEquiv h (d εA a) = d εB (algebraMap A B a) := map_d _ h a

lemma map_bijective_of_isLocalization (M : Submonoid A) [IsLocalization M B]
    (h : εB.comp (IsScalarTower.toAlgHom R A B) = εA) : Function.Bijective (map _ h) :=
  haveI := Algebra.FormallyEtale.of_isLocalization (Rₘ := B) M
  map_bijective h

variable (εA B) in

def locAug (M : Submonoid A) [IsLocalization M B] (hM : ∀ m : M, IsUnit (εA m)) : B →ₐ[R] R :=
  IsLocalization.liftAlgHom (M := M) (f := εA) hM

lemma locAug_comp (M : Submonoid A) [IsLocalization M B] (hM : ∀ m : M, IsUnit (εA m)) :
    (locAug B εA M hM).comp (IsScalarTower.toAlgHom R A B) = εA := by
  ext a; simp [locAug]

variable (εA B) in

def locEquiv (M : Submonoid A) [IsLocalization M B] (hM : ∀ m : M, IsUnit (εA m)) :
    AugCot εA ≃ₗ[R] AugCot (locAug B εA M hM) :=
  LinearEquiv.ofBijective (map _ (locAug_comp M hM)) (map_bijective_of_isLocalization M _)

@[simp] lemma locEquiv_d (M : Submonoid A) [IsLocalization M B] (hM : ∀ m : M, IsUnit (εA m))
    (a : A) : locEquiv B εA M hM (d εA a) = d _ (algebraMap A B a) :=
  map_d _ (locAug_comp M hM) a

variable (εA B) in

def awayAug (f : A) [IsLocalization.Away f B] (hf : IsUnit (εA f)) : B →ₐ[R] R :=
  locAug B εA (Submonoid.powers f) (by rintro ⟨_, n, rfl⟩; simpa using hf.pow n)

lemma awayAug_comp (f : A) [IsLocalization.Away f B] (hf : IsUnit (εA f)) :
    (awayAug B εA f hf).comp (IsScalarTower.toAlgHom R A B) = εA := locAug_comp _ _

variable (εA B) in

def awayEquiv (f : A) [IsLocalization.Away f B] (hf : IsUnit (εA f)) :
    AugCot εA ≃ₗ[R] AugCot (awayAug B εA f hf) := locEquiv B εA _ _

@[simp] lemma awayEquiv_d (f : A) [IsLocalization.Away f B] (hf : IsUnit (εA f)) (a : A) :
    awayEquiv B εA f hf (d εA a) = d _ (algebraMap A B a) := map_d _ (awayAug_comp f hf) a

end Tower

variable (εA εB) in

abbrev tensorAug : A ⊗[R] B →ₐ[R] R := Algebra.TensorProduct.productMap εA εB

lemma tensorAug_comp_includeLeft :
    (tensorAug εA εB).comp Algebra.TensorProduct.includeLeft = εA :=
  Algebra.TensorProduct.productMap_left _ _

lemma tensorAug_comp_includeRight :
    (tensorAug εA εB).comp Algebra.TensorProduct.includeRight = εB :=
  Algebra.TensorProduct.productMap_right _ _

lemma d_tmul (a : A) (b : B) : d (tensorAug εA εB) (a ⊗ₜ b) =
    εB b • d (tensorAug εA εB) (a ⊗ₜ 1) + εA a • d (tensorAug εA εB) (1 ⊗ₜ b) := by
  have : a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b) := by simp
  rw [this, d_mul, add_comm]
  simp

variable (εA εB) in

def tensorEquiv : AugCot (tensorAug εA εB) ≃ₗ[R] AugCot εA × AugCot εB :=
  LinearEquiv.ofLinear
    (LinearMap.prod
      (map (Algebra.TensorProduct.productMap (AlgHom.id R A) ((Algebra.ofId R A).comp εB))
        (by ext <;> simp))
      (map (Algebra.TensorProduct.productMap ((Algebra.ofId R B).comp εA) (AlgHom.id R B))
        (by ext <;> simp)))
    (LinearMap.coprod (map _ tensorAug_comp_includeLeft) (map _ tensorAug_comp_includeRight))
    (by
      refine LinearMap.prod_ext (hom_ext fun a => ?_) (hom_ext fun b => ?_) <;> simp)
    (hom_ext fun x => by
      induction x with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul a b => simp [d_mul, d_tmul a b])

@[simp] lemma tensorEquiv_symm_apply (x : AugCot εA) (y : AugCot εB) :
    (tensorEquiv εA εB).symm (x, y) =
      map _ tensorAug_comp_includeLeft x + map _ tensorAug_comp_includeRight y := rfl

@[simp] lemma tensorEquiv_d_tmul (a : A) (b : B) :
    tensorEquiv εA εB (d _ (a ⊗ₜ b)) = (εB b • d εA a, εA a • d εB b) := by
  rw [← LinearEquiv.eq_symm_apply, tensorEquiv_symm_apply, d_tmul]
  simp

end Map

section BaseChange

variable {R R' A A' : Type*} [CommRing R] [CommRing R'] [CommRing A] [CommRing A']
  [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra R A'] [IsScalarTower R R' A']
  {ε : A →ₐ[R] R} {ε' : A' →ₐ[R'] R'}

def mapBase (φ : A →ₐ[R] A') (h : ∀ a, ε' (φ a) = algebraMap R R' (ε a)) :
    AugCot ε →ₗ[R] AugCot ε' :=
  lift ε ((d ε').restrictScalars R ∘ₗ φ.toLinearMap) (fun a b => by simp [d_mul, h])

@[simp] lemma mapBase_d (φ : A →ₐ[R] A') (h : ∀ a, ε' (φ a) = algebraMap R R' (ε a)) (a : A) :
    mapBase φ h (d ε a) = d ε' (φ a) := lift_d ε _ _ a

lemma isBaseChange_mapBase (φ : A →ₐ[R] A') (h : ∀ a, ε' (φ a) = algebraMap R R' (ε a))
    (hφ : IsBaseChange R' φ.toLinearMap) : IsBaseChange R' (mapBase φ h) := by
  let D : A' →ₗ[R'] R' ⊗[R] AugCot ε := hφ.lift (TensorProduct.mk R R' (AugCot ε) 1 ∘ₗ d ε)
  have hD : ∀ a, D (φ a) = 1 ⊗ₜ d ε a := fun a => hφ.lift_eq _ a
  have hmul : ∀ x y, D (x * y) = ε' x • D y + ε' y • D x := by
    intro x y
    induction x using hφ.inductionOn with
    | zero => simp
    | add x x' hx hx' => simp only [add_mul, map_add, hx, hx', add_smul, smul_add]; abel
    | smul s x hx =>
      rw [smul_mul_assoc, map_smul, hx, map_smul, map_smul, smul_add, smul_assoc,
        smul_comm s (ε' y)]
    | tmul a =>
      induction y using hφ.inductionOn with
      | zero => simp
      | add x x' hx hx' => simp only [mul_add, map_add, hx, hx', add_smul, smul_add]; abel
      | smul s x hx =>
        rw [mul_smul_comm, map_smul, hx, map_smul, map_smul, smul_add, smul_assoc, smul_comm s]
      | tmul b =>
        simp only [AlgHom.toLinearMap_apply, ← map_mul, hD, h, d_mul, tmul_add, tmul_smul,
          algebraMap_smul]
  refine IsBaseChange.of_equiv
    (LinearEquiv.ofLinear (LinearMap.liftBaseChange R' (mapBase φ h)) (lift ε' D hmul)
      (hom_ext fun x => ?_) (LinearMap.ext fun x => ?_)) (fun x => by simp)
  · induction x using hφ.inductionOn with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, hx, hx']
    | smul s x hx => simp only [map_smul, hx]
    | tmul a => simp [hD]
  · induction x with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, hx, hx']
    | tmul s x =>
      obtain ⟨a, rfl⟩ := d_surjective ε x
      simp [hD, smul_tmul']

lemma isBaseChange_of_isPushout [Algebra A A'] [IsScalarTower R A A']
    [hP : Algebra.IsPushout R R' A A']
    (h : ∀ a, ε' (IsScalarTower.toAlgHom R A A' a) = algebraMap R R' (ε a)) :
    IsBaseChange R' (mapBase (IsScalarTower.toAlgHom R A A') h) :=
  isBaseChange_mapBase _ h hP.out

variable (R' ε) in

def baseChangeAug : R' ⊗[R] A →ₐ[R'] R' :=
  Algebra.TensorProduct.lift (AlgHom.id R' R') ((Algebra.ofId R R').comp ε)
    (fun _ _ => Commute.all _ _)

@[simp] lemma baseChangeAug_tmul (r : R') (a : A) :
    baseChangeAug R' ε (r ⊗ₜ a) = r * algebraMap R R' (ε a) := by
  simp [baseChangeAug]

variable (R' ε) in
lemma isBaseChange_baseChangeAug :
    IsBaseChange R' (mapBase (ε := ε) (ε' := baseChangeAug R' ε)
      Algebra.TensorProduct.includeRight (fun a => by simp)) :=
  isBaseChange_mapBase _ _ (TensorProduct.isBaseChange R A R')

variable (R' ε) in

def baseChangeEquiv : R' ⊗[R] AugCot ε ≃ₗ[R'] AugCot (baseChangeAug R' ε) :=
  (isBaseChange_baseChangeAug R' ε).equiv

@[simp] lemma baseChangeEquiv_tmul_d (r : R') (a : A) :
    baseChangeEquiv R' ε (r ⊗ₜ d ε a) = r • d _ (1 ⊗ₜ a) := by
  simp [baseChangeEquiv, IsBaseChange.equiv_tmul]

end BaseChange

section Smooth

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (ε : A →ₐ[R] R)

lemma finite_of_kaehler [Module.Finite A Ω[A⁄R]] : Module.Finite R (AugCot ε) := by
  letI : Algebra A R := (ε : A →+* R).toAlgebra
  exact Module.Finite.equiv (kaehlerEquiv ε (fun _ => rfl)).symm

lemma projective_of_kaehler [Module.Projective A Ω[A⁄R]] : Module.Projective R (AugCot ε) := by
  letI : Algebra A R := (ε : A →+* R).toAlgebra
  exact Module.Projective.of_equiv (kaehlerEquiv ε (fun _ => rfl)).symm

lemma free_of_kaehler [Module.Free A Ω[A⁄R]] : Module.Free R (AugCot ε) := by
  letI : Algebra A R := (ε : A →+* R).toAlgebra
  exact Module.Free.of_equiv (kaehlerEquiv ε (fun _ => rfl)).symm

lemma finrank_eq_of_free [Nontrivial R] [Module.Free A Ω[A⁄R]] :
    Module.finrank R (AugCot ε) = Module.finrank A Ω[A⁄R] := by
  letI : Algebra A R := (ε : A →+* R).toAlgebra
  haveI : Nontrivial A := (ε : A →+* R).domain_nontrivial
  rw [(kaehlerEquiv ε (fun _ => rfl)).finrank_eq, Module.finrank_baseChange]

instance finite [Algebra.EssFiniteType R A] : Module.Finite R (AugCot ε) := finite_of_kaehler ε

instance projective [Algebra.FormallySmooth R A] : Module.Projective R (AugCot ε) :=
  projective_of_kaehler ε

lemma rankAtStalk_eq [Module.Finite A Ω[A⁄R]] [Module.Flat A Ω[A⁄R]] (p : PrimeSpectrum R) :
    Module.rankAtStalk (AugCot ε) p = Module.rankAtStalk Ω[A⁄R] (p.comap (ε : A →+* R)) := by
  letI : Algebra A R := (ε : A →+* R).toAlgebra
  rw [Module.rankAtStalk_eq_of_equiv (kaehlerEquiv ε (fun _ => rfl)),
    Module.rankAtStalk_baseChange]
  rfl

instance free_of_isLocalRing [IsLocalRing R] [Algebra.FormallySmooth R A]
    [Algebra.EssFiniteType R A] : Module.Free R (AugCot ε) :=
  Module.free_of_flat_of_isLocalRing

instance free_of_isStandardSmooth [Algebra.IsStandardSmooth R A] : Module.Free R (AugCot ε) :=
  free_of_kaehler ε

lemma finrank_kaehler_of_isStandardSmoothOfRelativeDimension [Nontrivial A] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R A] : Module.finrank A Ω[A⁄R] = n := by
  rw [Module.finrank, Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n]
  simp

lemma finrank_of_isStandardSmoothOfRelativeDimension [Nontrivial R] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R A] : Module.finrank R (AugCot ε) = n := by
  haveI := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n (R := R) (S := A)
  haveI : Nontrivial A := (ε : A →+* R).domain_nontrivial
  rw [finrank_eq_of_free, finrank_kaehler_of_isStandardSmoothOfRelativeDimension n]

lemma nonempty_basis_of_isStandardSmoothOfRelativeDimension (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R A] :
    Nonempty (Module.Basis (Fin n) R (AugCot ε)) := by
  haveI := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n (R := R) (S := A)
  cases subsingleton_or_nontrivial R
  · haveI := Module.subsingleton R (AugCot ε)
    exact ⟨⟨LinearEquiv.ofSubsingleton _ _⟩⟩
  · exact ⟨Module.finBasisOfFinrankEq _ _ (finrank_of_isStandardSmoothOfRelativeDimension ε n)⟩

end Smooth

section RelDim

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (ε : A →ₐ[R] R) {n : ℕ}

lemma smooth_of_locally
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R A)) :
    Algebra.Smooth R A := by
  rw [← RingHom.smooth_algebraMap, RingHom.smooth_iff_locally_isStandardSmooth]
  exact RingHom.locally_of_locally
    (fun hf => RingHom.IsStandardSmoothOfRelativeDimension.isStandardSmooth n _ hf) h

lemma rankAtStalk_kaehler_of_locally
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R A))
    (q : PrimeSpectrum A) : Module.rankAtStalk Ω[A⁄R] q = n := by
  haveI := smooth_of_locally h
  obtain ⟨s, hs, H⟩ := h
  obtain ⟨t, hts, htq⟩ : ∃ t ∈ s, t ∉ q.asIdeal := by
    by_contra! hc
    exact q.2.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 hc))
  have hq : q ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away t))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away t) t]
    exact htq
  obtain ⟨q', rfl⟩ := hq
  have Ht := H t hts
  rw [← IsScalarTower.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at Ht
  haveI := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n (R := R)
    (S := Localization.Away t)
  haveI : Nontrivial (Localization.Away t) := q'.nontrivial
  haveI := Algebra.FormallyEtale.of_isLocalization (Rₘ := Localization.Away t) (Submonoid.powers t)
  rw [← Module.rankAtStalk_baseChange, Module.rankAtStalk_eq_of_equiv
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A (Localization.Away t)),
    Module.rankAtStalk_eq_finrank_of_free,
    finrank_kaehler_of_isStandardSmoothOfRelativeDimension n]
  rfl

lemma rankAtStalk_of_locally
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R A))
    (p : PrimeSpectrum R) : Module.rankAtStalk (AugCot ε) p = n := by
  haveI := smooth_of_locally h
  rw [rankAtStalk_eq, rankAtStalk_kaehler_of_locally h]

lemma finrank_of_locally [IsLocalRing R]
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R A)) :
    Module.finrank R (AugCot ε) = n := by
  haveI := smooth_of_locally h
  have := rankAtStalk_of_locally ε h (IsLocalRing.closedPoint R)
  rwa [Module.rankAtStalk_eq_finrank_of_free] at this

lemma nonempty_basis_of_locally [IsLocalRing R]
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R A)) :
    Nonempty (Module.Basis (Fin n) R (AugCot ε)) :=
  haveI := smooth_of_locally h
  ⟨Module.finBasisOfFinrankEq _ _ (finrank_of_locally ε h)⟩

open AlgebraicGeometry in

lemma locally_iff_smoothOfRelativeDimension :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R A) ↔
      SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
  (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)
    (φ := CommRingCat.ofHom (algebraMap R A))).symm

end RelDim

section Affine

variable {R σ : Type*} [CommRing R] (x : σ → R)

open MvPolynomial

def mvPolynomialBasis : Module.Basis σ R (AugCot (aeval x : MvPolynomial σ R →ₐ[R] R)) :=
  letI : Algebra (MvPolynomial σ R) R :=
    ((aeval x : MvPolynomial σ R →ₐ[R] R) : MvPolynomial σ R →+* R).toAlgebra
  ((KaehlerDifferential.mvPolynomialBasis R σ).baseChange R).map
    (kaehlerEquiv (aeval x : MvPolynomial σ R →ₐ[R] R) (fun _ => rfl)).symm

@[simp] lemma mvPolynomialBasis_apply (i : σ) :
    mvPolynomialBasis x i = d (aeval x : MvPolynomial σ R →ₐ[R] R) (X i) := by
  letI : Algebra (MvPolynomial σ R) R :=
    ((aeval x : MvPolynomial σ R →ₐ[R] R) : MvPolynomial σ R →+* R).toAlgebra
  simp only [mvPolynomialBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply]
  exact (LinearEquiv.symm_apply_eq _).2 (kaehlerEquiv_d _ _ _).symm

end Affine

end AugCot

open AugCot in

theorem augCot_properties.{u} {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (ε : A →ₐ[R] R) :

    (∀ a : A, d ε a = (RingHom.ker ε).toCotangent
      ⟨a - algebraMap R A (ε a), by simp [RingHom.mem_ker]⟩) ∧

    (letI : Algebra A R := (ε : A →+* R).toAlgebra
     ∃ e : AugCot ε ≃ₗ[R] R ⊗[A] Ω[A⁄R],
      ∀ a, e (d ε a) = 1 ⊗ₜ KaehlerDifferential.D R A a) ∧

    (∀ (N : Type u) [AddCommGroup N] [Module R N],
      letI : Module A N := Module.compHom N (ε : A →+* R)
      haveI : IsScalarTower R A N := isScalarTower_of_smul_eq ε fun _ _ => rfl
      ∃ e : Derivation R A N ≃ₗ[R] (AugCot ε →ₗ[R] N), ∀ D a, e D (d ε a) = D a) ∧

    (∀ (N : Type u) [AddCommGroup N] [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N],
      ∃ e : {φ : A →ₐ[R] TrivSqZeroExt R N // (TrivSqZeroExt.fstHom R R N).comp φ = ε} ≃
        (AugCot ε →ₗ[R] N), ∀ φ a, e φ (d ε a) = (φ.1 a).snd) ∧

    (∀ (R' : Type u) [CommRing R'] [Algebra R R'],
      (∀ r a, baseChangeAug R' ε (r ⊗ₜ a) = r * algebraMap R R' (ε a)) ∧
      ∃ e : R' ⊗[R] AugCot ε ≃ₗ[R'] AugCot (baseChangeAug R' ε),
        ∀ r a, e (r ⊗ₜ d ε a) = r • d _ (1 ⊗ₜ a)) ∧

    (map (AlgHom.id R A) (AlgHom.comp_id ε) = LinearMap.id) ∧
    (∀ (B : Type u) [CommRing B] [Algebra R B] (εB : B →ₐ[R] R) (φ : A →ₐ[R] B)
      (h : εB.comp φ = ε),
      (∀ a, map φ h (d ε a) = d εB (φ a)) ∧
      (∀ (C : Type u) [CommRing C] [Algebra R C] (εC : C →ₐ[R] R) (ψ : B →ₐ[R] C)
        (h' : εC.comp ψ = εB) (h'' : εC.comp (ψ.comp φ) = ε),
        map (ψ.comp φ) h'' = map ψ h' ∘ₗ map φ h) ∧

      ((φ : A →+* B).Etale → Function.Bijective (map φ h)) ∧

      (Function.Surjective φ →
        (∀ x : RingHom.ker φ, kerMap φ h x = (RingHom.ker ε).toCotangent ⟨x, ker_le φ h x.2⟩) ∧
        Function.Exact (kerMap φ h) (map φ h) ∧ Function.Surjective (map φ h))) ∧

    (∀ (f : A) (B : Type u) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
      [IsLocalization.Away f B],
      (IsUnit (ε f) → ∃ εB : B →ₐ[R] R, εB.comp (IsScalarTower.toAlgHom R A B) = ε) ∧
      ∀ (εB : B →ₐ[R] R) (h : εB.comp (IsScalarTower.toAlgHom R A B) = ε),
        Function.Bijective (map _ h)) ∧

    (∀ (B : Type u) [CommRing B] [Algebra R B] (εB : B →ₐ[R] R),
      ∃ e : AugCot (Algebra.TensorProduct.productMap ε εB) ≃ₗ[R] AugCot ε × AugCot εB,
        ∀ a b, e (d _ (a ⊗ₜ b)) = (εB b • d ε a, ε a • d εB b)) ∧

    (Algebra.Smooth R A → Module.Finite R (AugCot ε) ∧ Module.Projective R (AugCot ε) ∧
      (IsLocalRing R → Module.Free R (AugCot ε))) ∧
    (Algebra.IsStandardSmooth R A → Module.Free R (AugCot ε)) ∧
    (∀ n : ℕ, Algebra.IsStandardSmoothOfRelativeDimension n R A →
      Nonempty (Module.Basis (Fin n) R (AugCot ε))) ∧
    (∀ n : ℕ, AlgebraicGeometry.SmoothOfRelativeDimension n
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R A))) →
      Algebra.Smooth R A ∧ (∀ p : PrimeSpectrum R, Module.rankAtStalk (AugCot ε) p = n) ∧
      (IsLocalRing R → Nonempty (Module.Basis (Fin n) R (AugCot ε)))) := by
  refine ⟨fun a => rfl, ?_, fun N _ _ => ?_, fun N _ _ _ _ => ⟨sqZeroEquiv ε N, sqZeroEquiv_d ε⟩,
    fun R' _ _ => ⟨baseChangeAug_tmul, baseChangeEquiv R' ε, baseChangeEquiv_tmul_d⟩, map_id,
    fun B _ _ εB φ h => ⟨map_d φ h, fun C _ _ εC ψ h' h'' => map_comp φ ψ h h' h'',
      map_bijective_of_etale φ h,
      fun hφ => ⟨fun _ => rfl, exact_kerMap_map φ h hφ, map_surjective φ h hφ⟩⟩,
    fun f B _ _ _ _ _ => ⟨fun hf => ⟨awayAug B ε f hf, awayAug_comp f hf⟩,
      fun εB h => map_bijective_of_isLocalization (Submonoid.powers f) h⟩,
    fun B _ _ εB => ⟨tensorEquiv ε εB, tensorEquiv_d_tmul⟩,
    fun _ => ⟨inferInstance, inferInstance, fun _ => inferInstance⟩, fun _ => inferInstance,
    fun n _ => nonempty_basis_of_isStandardSmoothOfRelativeDimension ε n, fun n hn => ?_⟩
  · letI : Algebra A R := (ε : A →+* R).toAlgebra
    exact ⟨kaehlerEquiv ε fun _ => rfl, kaehlerEquiv_d ε _⟩
  · letI : Module A N := Module.compHom N (ε : A →+* R)
    haveI : IsScalarTower R A N := isScalarTower_of_smul_eq ε fun _ _ => rfl
    exact ⟨derivationEquiv ε fun _ _ => rfl, derivationEquiv_d ε _⟩
  · have h := locally_iff_smoothOfRelativeDimension.2 hn
    exact ⟨smooth_of_locally h, rankAtStalk_of_locally ε h,
      fun _ => nonempty_basis_of_locally ε h⟩

end GlobalTheory
