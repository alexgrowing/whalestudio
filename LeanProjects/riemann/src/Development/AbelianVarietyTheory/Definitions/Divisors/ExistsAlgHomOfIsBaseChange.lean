import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AlternatingMapSumSmulEqDetSmul

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace GlobalTheory

namespace TopForm

section BaseChange

variable {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]

def extProj (A M : Type*) [CommRing A] [AddCommGroup M] [Module A M] (D : ℕ) :
    ExteriorAlgebra A M →ₗ[A] ⋀[A]^D M :=
  (DirectSum.component A ℕ (fun i => ⋀[A]^i M) D).comp
    (DirectSum.decomposeLinearEquiv (fun i => ⋀[A]^i M)).toLinearMap

theorem extProj_coe (D : ℕ) (x : ⋀[A]^D M) : extProj A M D x = x := by
  change (DirectSum.decompose (fun i => ⋀[A]^i M) (x : ExteriorAlgebra A M)) D = x
  rw [DirectSum.decompose_coe, DirectSum.of_eq_same]

theorem exists_algHom_of_isBaseChange {φ : M →ₗ[A] N} (hφ : IsBaseChange B φ) :
    ∃ F : ExteriorAlgebra B N →ₐ[B] B ⊗[A] ExteriorAlgebra A M,
      ∀ m, F (ExteriorAlgebra.ι B (φ m)) = 1 ⊗ₜ ExteriorAlgebra.ι A m := by
  let f : N →ₗ[B] B ⊗[A] ExteriorAlgebra A M :=
    hφ.lift ((TensorProduct.mk A B _ 1).comp (ExteriorAlgebra.ι A))
  have hf (m : M) : f (φ m) = 1 ⊗ₜ ExteriorAlgebra.ι A m := hφ.lift_eq _ m
  have anti (n n' : N) : f n * f n' + f n' * f n = 0 := by
    induction n using hφ.inductionOn with
    | zero => simp
    | smul s n h => rw [map_smul, smul_mul_assoc, mul_smul_comm, ← smul_add, h, smul_zero]
    | add a b ha hb => rw [map_add, add_mul, mul_add, add_add_add_comm, ha, hb, add_zero]
    | tmul m =>
      induction n' using hφ.inductionOn with
      | zero => simp
      | smul s n h => rw [map_smul, smul_mul_assoc, mul_smul_comm, ← smul_add, h, smul_zero]
      | add a b ha hb => rw [map_add, add_mul, mul_add, add_add_add_comm, ha, hb, add_zero]
      | tmul m' =>
        rw [hf, hf, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          ← TensorProduct.tmul_add, ExteriorAlgebra.ι_add_mul_swap, TensorProduct.tmul_zero]
  have sq (n : N) : f n * f n = 0 := by
    induction n using hφ.inductionOn with
    | zero => simp
    | smul s n h => rw [map_smul, smul_mul_assoc, mul_smul_comm, h, smul_zero, smul_zero]
    | add a b ha hb =>
      rw [map_add, add_mul, mul_add, mul_add, ha, hb, zero_add, add_zero, anti]
    | tmul m =>
      rw [hf, Algebra.TensorProduct.tmul_mul_tmul, ExteriorAlgebra.ι_sq_zero,
        TensorProduct.tmul_zero]
  exact ⟨ExteriorAlgebra.lift B ⟨f, sq⟩, fun m => by rw [ExteriorAlgebra.lift_ι_apply, hf]⟩

theorem isBaseChange_exteriorPower {φ : M →ₗ[A] N} (hφ : IsBaseChange B φ) (D : ℕ) :
    IsBaseChange B (exteriorPowerMapOver B D φ) := by
  obtain ⟨F, hF⟩ := exists_algHom_of_isBaseChange hφ
  let G : (⋀[B]^D N) →ₗ[B] B ⊗[A] (⋀[A]^D M) :=
    ((extProj A M D).baseChange B) ∘ₗ F.toLinearMap ∘ₗ (⋀[B]^D N).subtype
  let H : B ⊗[A] (⋀[A]^D M) →ₗ[B] ⋀[B]^D N := (exteriorPowerMapOver B D φ).liftBaseChange B
  have hG (x : ⋀[A]^D M) : G (exteriorPowerMapOver B D φ x) = 1 ⊗ₜ x := by
    have : (G.restrictScalars A) ∘ₗ (exteriorPowerMapOver B D φ) = TensorProduct.mk A B _ 1 := by
      apply exteriorPower.linearMap_ext
      ext1 v
      have e : F (ExteriorAlgebra.ιMulti B D fun k => φ (v k)) =
          1 ⊗ₜ ExteriorAlgebra.ιMulti A D v := by
        rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod,
          List.map_ofFn]
        have := map_list_prod (Algebra.TensorProduct.includeRight (R := A) (A := B)
          (B := ExteriorAlgebra A M)) (List.ofFn fun i => ExteriorAlgebra.ι A (v i))
        rw [Algebra.TensorProduct.includeRight_apply, List.map_ofFn] at this
        rw [this]
        congr 2
        funext k
        exact hF _
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
        exteriorPowerMapOver_ιMulti, LinearMap.restrictScalars_apply, G, Submodule.subtype_apply,
        exteriorPower.ιMulti_apply_coe, AlgHom.toLinearMap_apply, e, LinearMap.baseChange_tmul,
        TensorProduct.mk_apply]
      rw [← exteriorPower.ιMulti_apply_coe, extProj_coe]
    exact LinearMap.congr_fun this x
  have h1 : G ∘ₗ H = LinearMap.id := by
    refine TensorProduct.AlgebraTensorModule.ext fun b x => ?_
    simp [H, hG, TensorProduct.smul_tmul']
  have h2 : Function.Surjective H := by
    rw [← LinearMap.range_eq_top, eq_top_iff,
      ← exteriorPower.ιMulti_span_of_span B D N (s := Set.range φ) (by
        rw [eq_top_iff]
        rintro n -
        induction n using hφ.inductionOn with
        | zero => simp
        | smul s n h => exact Submodule.smul_mem _ _ h
        | add a b ha hb => exact add_mem ha hb
        | tmul m => exact Submodule.subset_span ⟨m, rfl⟩), Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    choose v hv using fun k => hw (Set.mem_range_self k)
    refine ⟨1 ⊗ₜ exteriorPower.ιMulti A D v, ?_⟩
    simp [H, hv]
  have h3 : Function.Injective H :=
    Function.LeftInverse.injective (g := G) fun x => LinearMap.congr_fun h1 x
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective H ⟨h3, h2⟩) fun x => by
    change H _ = _
    simp [H]

def IsFreeGen (A : Type*) {M : Type*} [CommRing A] [AddCommGroup M] [Module A M] (ω : M) : Prop :=
  Function.Bijective fun a : A => a • ω

theorem IsFreeGen.of_isBaseChange {φ : M →ₗ[A] N} (hφ : IsBaseChange B φ) {ω : M}
    (h : IsFreeGen A ω) : IsFreeGen B (φ ω) := by
  let e : A ≃ₗ[A] M := LinearEquiv.ofBijective (LinearMap.toSpanSingleton A M ω) h
  let e' : B ≃ₗ[B] N := (Algebra.TensorProduct.rid A B B).symm.toLinearEquiv ≪≫ₗ
    (e.baseChange A B A M) ≪≫ₗ hφ.equiv
  have : (fun b : B => b • φ ω) = e' := by
    funext b
    have he : e 1 = ω := one_smul A ω
    simp [e', he]
  rw [IsFreeGen, this]
  exact e'.bijective

theorem isFreeGen_ιMulti {D : ℕ} (b : Module.Basis (Fin D) A M) :
    IsFreeGen A (exteriorPower.ιMulti A D b) := by
  have key : (LinearMap.toSpanSingleton A _ (exteriorPower.ιMulti A D b)) ∘ₗ
      exteriorPower.alternatingMapLinearEquiv b.det = LinearMap.id := by
    apply exteriorPower.linearMap_ext
    refine Module.Basis.ext_alternating b fun v hv => ?_
    have hb : Function.Bijective v := Finite.injective_iff_bijective.mp hv
    let σ : Equiv.Perm (Fin D) := Equiv.ofBijective v hb
    have e1 : (fun i => b (v i)) = b ∘ σ := rfl
    rw [e1, AlternatingMap.map_perm, AlternatingMap.map_perm]
    simp [Module.Basis.det_self]
  refine ⟨fun a a' h => ?_, fun x => ⟨_, LinearMap.congr_fun key x⟩⟩
  simpa [Module.Basis.det_self] using congrArg (exteriorPower.alternatingMapLinearEquiv b.det) h

end BaseChange

section FreeGen

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] {ω : M}

def IsFreeGen.repr (h : IsFreeGen A ω) : M ≃ₗ[A] A :=
  (LinearEquiv.ofBijective (LinearMap.toSpanSingleton A M ω) h).symm

theorem IsFreeGen.repr_smul (h : IsFreeGen A ω) (x : M) : h.repr x • ω = x :=
  h.repr.symm_apply_apply x

theorem IsFreeGen.unit_smul (h : IsFreeGen A ω) (u : Aˣ) : IsFreeGen A ((u : A) • ω) := by
  have : (fun a : A => a • (u : A) • ω) = (fun a : A => a • ω) ∘ (· * (u : A)) := by
    funext a
    exact (mul_smul _ _ _).symm
  rw [IsFreeGen, this]
  exact h.comp u.mulRight.bijective

theorem IsFreeGen.smul_iff (h : IsFreeGen A ω) {a : A} : IsFreeGen A (a • ω) ↔ IsUnit a := by
  refine ⟨fun h' => ?_, fun ⟨u, hu⟩ => hu ▸ h.unit_smul u⟩
  obtain ⟨b, hb⟩ := h'.2 ω
  refine IsUnit.of_mul_eq_one b (h.1 ?_)
  simpa only [mul_comm a b, mul_smul, one_smul] using hb

end FreeGen

section Ring

variable {k A B C : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing C]

abbrev Omega (α : k →+* A) : Type _ := letI := α.toAlgebra; Ω[A⁄k]

abbrev Forms (α : k →+* A) (D : ℕ) : Type _ := ⋀[A]^D (Omega α)

abbrev dFun (α : k →+* A) (f : A) : Omega α := letI := α.toAlgebra; KaehlerDifferential.D k A f

variable {D : ℕ}

def dForm (α : k →+* A) (f : Fin D → A) : Forms α D := letI := α.toAlgebra; dWedge k f

theorem dForm_eq (α : k →+* A) (f : Fin D → A) :
    dForm α f = exteriorPower.ιMulti A D fun i => dFun α (f i) := rfl

variable {α : k →+* A} {β : k →+* B} {γ : k →+* C}

theorem span_dForm (α : k →+* A) (D : ℕ) :
    Submodule.span A (Set.range (dForm α (D := D))) = ⊤ := by
  letI := α.toAlgebra
  rw [eq_top_iff, ← exteriorPower.ιMulti_span_of_span A D (Omega α)
    (KaehlerDifferential.span_range_derivation k A)]
  refine Submodule.span_mono ?_
  rintro _ ⟨w, hw, rfl⟩
  choose v hv using fun i => hw (Set.mem_range_self i)
  exact ⟨v, congrArg (exteriorPower.ιMulti A D) (funext hv)⟩

variable (D) in

def formMap (ρ : A →+* B) (h : ρ.comp α = β) : Forms α D →ₛₗ[ρ] Forms β D :=
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' h.symm
  { toFun := exteriorPowerMapOver B D (KaehlerDifferential.map k k A B)
    map_add' := map_add _
    map_smul' := fun a x => by
      rw [map_smul, ← algebraMap_smul B]
      rfl }

@[simp] theorem formMap_dForm (ρ : A →+* B) (h : ρ.comp α = β) (f : Fin D → A) :
    formMap D ρ h (dForm α f) = dForm β fun i => ρ (f i) := by
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' h.symm
  change exteriorPowerMapOver B D (KaehlerDifferential.map k k A B) (exteriorPower.ιMulti A D _) = _
  rw [exteriorPowerMapOver_ιMulti, dForm_eq]
  simp only [KaehlerDifferential.map_D]
  rfl

theorem forms_ext {M : Type*} [AddCommGroup M] [Module B M] {ρ : A →+* B}
    {φ ψ : Forms α D →ₛₗ[ρ] M} (h : ∀ f, φ (dForm α f) = ψ (dForm α f)) : φ = ψ :=
  LinearMap.ext_on_range (span_dForm α D) h

theorem formMap_formMap (ρ : A →+* B) (σ : B →+* C) (τ : A →+* C) (e : σ.comp ρ = τ)
    (h : ρ.comp α = β) (h' : σ.comp β = γ) (h'' : τ.comp α = γ) (x : Forms α D) :
    formMap D σ h' (formMap D ρ h x) = formMap D τ h'' x := by
  haveI : RingHomCompTriple ρ σ τ := ⟨e⟩
  refine LinearMap.congr_fun (forms_ext (φ := (formMap D σ h').comp (formMap D ρ h))
    (ψ := formMap D τ h'') fun f => ?_) x
  rw [LinearMap.comp_apply, formMap_dForm, formMap_dForm, formMap_dForm, ← e]
  rfl

theorem formMap_of_eq_id (ρ : A →+* A) (e : ρ = RingHom.id A) (h : ρ.comp α = α) (x : Forms α D) :
    formMap D ρ h x = x := by
  subst e
  exact LinearMap.congr_fun (forms_ext (φ := formMap D _ h) (ψ := LinearMap.id)
    fun f => by simp) x

theorem IsFreeGen.formMap {ρ : A →+* B} (hρ : ρ.Etale) (h : ρ.comp α = β) {ω : Forms α D}
    (hω : IsFreeGen A ω) : IsFreeGen B (formMap D ρ h ω) := by
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' h.symm
  haveI : Algebra.Etale A B := hρ
  exact hω.of_isBaseChange (isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale k A B) D)

theorem isFreeGen_dForm (x : Fin D → A) (b : Module.Basis (Fin D) A (Omega α))
    (hb : ∀ i, b i = dFun α (x i)) : IsFreeGen A (dForm α x) := by
  have := isFreeGen_ιMulti b
  rwa [show (b : Fin D → Omega α) = fun i => dFun α (x i) from funext hb] at this

theorem exists_isFreeGen (h : α.IsStandardSmoothOfRelativeDimension D) :
    ∃ ω : Forms α D, IsFreeGen A ω := by
  letI := α.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension D k A := h
  cases subsingleton_or_nontrivial A with
  | inl _ =>
    haveI := Module.subsingleton A (Forms α D)
    exact ⟨0, fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  | inr _ =>
    haveI := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth D (R := k) (S := A)
    haveI : Module.Free A (Omega α) := inferInstanceAs (Module.Free A Ω[A⁄k])
    haveI : Module.Finite A (Omega α) := inferInstanceAs (Module.Finite A Ω[A⁄k])
    have hr : Module.finrank A (Omega α) = D := Module.finrank_eq_of_rank_eq
      (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := k) (S := A) D)
    exact ⟨_, isFreeGen_ιMulti (Module.finBasisOfFinrankEq A (Omega α) hr)⟩

theorem map_dForm_mul_sub_mem (c : Forms α D →ₗ[A] A) (I : Ideal A) (h : A) (g : Fin D → A)
    (hg : ∀ i, g i ∈ I) : c (dForm α fun i => h * g i) - h ^ D * c (dForm α g) ∈ I := by
  letI := α.toAlgebra
  have := Submodule.mem_map_of_mem (f := c) (dWedge_mul_sub_mem k I h g hg)
  rw [Submodule.map_smul'', map_sub, map_smul] at this
  exact (Submodule.smul_mono le_rfl le_top).trans
    (by rw [smul_eq_mul, Ideal.mul_top]) this

theorem dForm_eq_det_smul (f x : Fin D → A) (a : Matrix (Fin D) (Fin D) A)
    (h : ∀ i, dFun α (f i) = ∑ j, a i j • dFun α (x j)) : dForm α f = a.det • dForm α x := by
  rw [dForm_eq, dForm_eq, ← alternating_map_sum_smul_eq_det_smul]
  exact congrArg _ (funext h)

end Ring

end TopForm

end GlobalTheory
