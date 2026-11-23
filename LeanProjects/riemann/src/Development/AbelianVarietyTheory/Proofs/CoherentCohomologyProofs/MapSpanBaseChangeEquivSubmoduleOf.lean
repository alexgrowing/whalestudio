import Mathlib

open TensorProduct

namespace GlobalTheory

section General

variable {R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]
variable {V V' : Type*} [AddCommGroup V] [Module R V] [AddCommGroup V'] [Module R V']

theorem baseChange_map (f : V →ₗ[R] V') (A : Submodule R V) :
    (A.map f).baseChange S = (A.baseChange S).map (f.baseChange S) := by
  simp only [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe,
    Set.image_image]
  rfl

theorem baseChange_range (f : V →ₗ[R] V') :
    (LinearMap.range f).baseChange S = LinearMap.range (f.baseChange S) := by
  rw [← Submodule.map_top, baseChange_map, Submodule.baseChange_top, Submodule.map_top]

theorem ker_baseChange_mkQ (B : Submodule R V) :
    LinearMap.ker (B.mkQ.baseChange S) = B.baseChange S := by
  rw [Submodule.baseChange, ← LinearMap.exact_iff]
  exact lTensor_exact S (LinearMap.exact_subtype_mkQ B) B.mkQ_surjective

noncomputable def baseChangeQuotEquiv (B : Submodule R V) :
    S ⊗[R] (V ⧸ B) ≃ₗ[S] (S ⊗[R] V) ⧸ B.baseChange S :=
  TensorProduct.AlgebraTensorModule.tensorQuotientEquiv S R S B

@[simp]
theorem baseChangeQuotEquiv_tmul (B : Submodule R V) (s : S) (x : V) :
    baseChangeQuotEquiv S B (s ⊗ₜ Submodule.Quotient.mk x) = Submodule.Quotient.mk (s ⊗ₜ x) :=
  rfl

variable [Module.Flat R S]

theorem baseChange_ker (f : V →ₗ[R] V') :
    (LinearMap.ker f).baseChange S = LinearMap.ker (f.baseChange S) := by
  rw [Submodule.baseChange, eq_comm, ← LinearMap.exact_iff]
  exact Module.Flat.lTensor_exact S (LinearMap.exact_subtype_ker_map f)

theorem baseChange_comap (f : V →ₗ[R] V') (B : Submodule R V') :
    (B.comap f).baseChange S = (B.baseChange S).comap (f.baseChange S) := by
  rw [← ker_baseChange_mkQ S B, ← LinearMap.ker_comp, ← LinearMap.baseChange_comp,
    ← baseChange_ker, LinearMap.ker_comp, Submodule.ker_mkQ]

theorem baseChange_inf (A B : Submodule R V) :
    (A ⊓ B).baseChange S = A.baseChange S ⊓ B.baseChange S := by
  rw [← Submodule.map_comap_subtype, baseChange_map, baseChange_comap, Submodule.map_comap_eq]
  rfl

theorem baseChange_iInf {ι : Type*} [Finite ι] (A : ι → Submodule R V) :
    (⨅ i, A i).baseChange S = ⨅ i, (A i).baseChange S := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih => rw [← e.iInf_comp, ← e.iInf_comp, ih]
  | h_empty => rw [iInf_of_empty, iInf_of_empty, Submodule.baseChange_top]
  | h_option ih => rw [iInf_option, iInf_option, baseChange_inf, ih]

theorem baseChange_injective {f : V →ₗ[R] V'} (hf : Function.Injective f) :
    Function.Injective (f.baseChange S) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := S) f hf

noncomputable def baseChangeEquiv (A : Submodule R V) : S ⊗[R] A ≃ₗ[S] A.baseChange S :=
  LinearEquiv.ofInjective (A.subtype.baseChange S) (baseChange_injective S A.injective_subtype)

@[simp]
theorem coe_baseChangeEquiv_apply (A : Submodule R V) (x : S ⊗[R] A) :
    (baseChangeEquiv S A x : S ⊗[R] V) = A.subtype.baseChange S x := rfl

theorem map_baseChangeEquiv_submoduleOf (A B : Submodule R V) :
    ((B.submoduleOf A).baseChange S).map (baseChangeEquiv S A : S ⊗[R] A →ₗ[S] A.baseChange S) =
      (B.baseChange S).submoduleOf (A.baseChange S) := by
  rw [Submodule.submoduleOf, baseChange_comap, Submodule.map_equiv_eq_comap_symm,
    ← Submodule.comap_comp, Submodule.submoduleOf]
  congr 1
  ext1 x
  obtain ⟨y, rfl⟩ := (baseChangeEquiv S A).surjective x
  simp

noncomputable def baseChangeSubquotEquiv (A B : Submodule R V) :
    S ⊗[R] (A ⧸ B.submoduleOf A) ≃ₗ[S]
      A.baseChange S ⧸ (B.baseChange S).submoduleOf (A.baseChange S) :=
  baseChangeQuotEquiv S (B.submoduleOf A) ≪≫ₗ
    Submodule.Quotient.equiv _ _ (baseChangeEquiv S A) (map_baseChangeEquiv_submoduleOf S A B)

@[simp]
theorem baseChangeSubquotEquiv_tmul (A B : Submodule R V) (s : S) (x : A) :
    baseChangeSubquotEquiv S A B (s ⊗ₜ Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨s ⊗ₜ (x : V), Submodule.tmul_mem_baseChange_of_mem s x.2⟩ :=
  rfl

theorem lift_rank_baseChange.{u, v, w} {R : Type u} (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] [NoZeroDivisors S] [FaithfulSMul R S]
    {V : Type w} [AddCommGroup V] [Module R V] (A : Submodule R V) :
    Cardinal.lift.{w} (Module.rank S (A.baseChange S)) = Cardinal.lift.{max v w} (Module.rank R A) := by
  rw [← (baseChangeEquiv S A).rank_eq]
  exact (TensorProduct.isBaseChange R A S).lift_rank_eq

theorem finrank_baseChange [NoZeroDivisors S] [FaithfulSMul R S] (A : Submodule R V) :
    Module.finrank S (A.baseChange S) = Module.finrank R A := by
  simpa using! congr_arg Cardinal.toNat (lift_rank_baseChange S A)

end General

section Lattice

variable {R : Type*} (K S L : Type*) [CommRing R] [Field K] [CommRing S] [CommRing L]
  [Algebra R K] [Algebra K L] [Algebra S L]
variable {V V' : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']

def spanBaseChange (M : Submodule R V) : Submodule S (L ⊗[K] V) :=
  Submodule.span S ((fun m => (1 : L) ⊗ₜ[K] m) '' (M : Set V))

variable [Algebra R S] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L]

variable (R V) in

noncomputable def baseChangeToField : S ⊗[R] V →ₗ[S] L ⊗[K] V :=
  LinearMap.liftBaseChange S ((TensorProduct.mk K L V 1).restrictScalars R)

@[simp]
theorem baseChangeToField_tmul (s : S) (v : V) :
    baseChangeToField R K S L V (s ⊗ₜ v) = algebraMap S L s ⊗ₜ[K] v := by
  simp [baseChangeToField, smul_tmul', Algebra.smul_def]

theorem baseChangeToField_naturality (f : V →ₗ[K] V') (x : S ⊗[R] V) :
    f.baseChange L (baseChangeToField R K S L V x) =
      baseChangeToField R K S L V' ((f.restrictScalars R).baseChange S x) := by
  induction x with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul s v => simp

theorem spanBaseChange_eq_map (M : Submodule R V) :
    spanBaseChange K S L M = (M.baseChange S).map (baseChangeToField R K S L V) := by
  simp only [spanBaseChange, Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe,
    Set.image_image, TensorProduct.mk_apply, baseChangeToField_tmul, map_one]

omit [Algebra R K] [IsScalarTower R K V] [IsScalarTower R K V'] [Algebra R S] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L] in

theorem spanBaseChange_map [LinearMap.CompatibleSMul V V' R K] (f : V →ₗ[K] V')
    (M : Submodule R V) :
    spanBaseChange K S L (M.map (f.restrictScalars R)) =
      (spanBaseChange K S L M).map ((f.baseChange L).restrictScalars S) := by
  simp only [spanBaseChange, Submodule.map_span, Submodule.map_coe, Set.image_image]
  rfl

variable [IsFractionRing R K] [FaithfulSMul S L]

variable (R V) in

theorem baseChangeToField_injective : Function.Injective (baseChangeToField R K S L V) := by
  have hflat : Module.Flat R V :=
    (Module.flat_iff_of_isLocalization K (nonZeroDivisors R) V).1 inferInstance
  have h1 : Function.Injective ((IsScalarTower.toAlgHom R S L).toLinearMap.rTensor V) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (FaithfulSMul.algebraMap_injective S L)
  have h2 : ∀ x, IsLocalization.moduleTensorEquiv (nonZeroDivisors R) K L V
      (baseChangeToField R K S L V x) = (IsScalarTower.toAlgHom R S L).toLinearMap.rTensor V x := by
    intro x
    induction x with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s v => rw [baseChangeToField_tmul]; rfl
  intro x y hxy
  apply h1
  rw [← h2, ← h2, hxy]

theorem comap_baseChangeToField (W : Submodule K V) :
    ((W.baseChange L).restrictScalars S).comap (baseChangeToField R K S L V) =
      (W.restrictScalars R).baseChange S := by
  ext x
  have hker : (W.restrictScalars R).baseChange S =
      LinearMap.ker ((W.mkQ.restrictScalars R).baseChange S) :=
    (ker_baseChange_mkQ S (W.restrictScalars R)).symm
  rw [Submodule.mem_comap, Submodule.restrictScalars_mem, ← ker_baseChange_mkQ L W, hker,
    LinearMap.mem_ker, LinearMap.mem_ker, baseChangeToField_naturality,
    map_eq_zero_iff _ (baseChangeToField_injective R K S L (V ⧸ W))]

variable [Module.Flat R S]

theorem spanBaseChange_inf_subspace (M : Submodule R V) (W : Submodule K V) :
    spanBaseChange K S L (M ⊓ W.restrictScalars R) =
      spanBaseChange K S L M ⊓ (W.baseChange L).restrictScalars S := by
  rw [spanBaseChange_eq_map, spanBaseChange_eq_map, baseChange_inf, ← comap_baseChangeToField K S L,
    Submodule.map_inf_eq_map_inf_comap]

noncomputable def spanBaseChangeEquiv (M : Submodule R V) :
    S ⊗[R] M ≃ₗ[S] spanBaseChange K S L M :=
  baseChangeEquiv S M ≪≫ₗ
    Submodule.equivMapOfInjective _ (baseChangeToField_injective R K S L V) _ ≪≫ₗ
    LinearEquiv.ofEq _ _ (spanBaseChange_eq_map K S L M).symm

@[simp]
theorem coe_spanBaseChangeEquiv_apply (M : Submodule R V) (x : S ⊗[R] M) :
    (spanBaseChangeEquiv K S L M x : L ⊗[K] V) =
      baseChangeToField R K S L V (M.subtype.baseChange S x) := rfl

theorem map_spanBaseChangeEquiv_submoduleOf (M N : Submodule R V) :
    ((N.submoduleOf M).baseChange S).map
        (spanBaseChangeEquiv K S L M : S ⊗[R] M →ₗ[S] spanBaseChange K S L M) =
      (spanBaseChange K S L N).submoduleOf (spanBaseChange K S L M) := by
  rw [Submodule.submoduleOf, baseChange_comap, Submodule.map_equiv_eq_comap_symm]
  ext x
  obtain ⟨y, rfl⟩ := (spanBaseChangeEquiv K S L M).surjective x
  rw [Submodule.submoduleOf, spanBaseChange_eq_map K S L N]
  simp only [Submodule.mem_comap, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    Submodule.subtype_apply, coe_spanBaseChangeEquiv_apply]
  exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨z, hz, h⟩ => baseChangeToField_injective R K S L V h ▸ hz⟩

noncomputable def spanBaseChangeSubquotEquiv (M N : Submodule R V) :
    S ⊗[R] (M ⧸ N.submoduleOf M) ≃ₗ[S]
      spanBaseChange K S L M ⧸ (spanBaseChange K S L N).submoduleOf (spanBaseChange K S L M) :=
  baseChangeQuotEquiv S (N.submoduleOf M) ≪≫ₗ
    Submodule.Quotient.equiv _ _ (spanBaseChangeEquiv K S L M)
      (map_spanBaseChangeEquiv_submoduleOf K S L M N)

theorem finrank_spanBaseChange [NoZeroDivisors S] [FaithfulSMul R S] (M : Submodule R V) :
    Module.finrank S (spanBaseChange K S L M) = Module.finrank R M := by
  rw [← (spanBaseChangeEquiv K S L M).finrank_eq]
  exact (TensorProduct.isBaseChange R M S).finrank_eq

end Lattice

theorem lift_rank_spanBaseChange.{u, v} {R : Type*} (K S : Type*) (L : Type u) [CommRing R]
    [Field K] [CommRing S] [CommRing L] [Algebra R K] [Algebra K L] [Algebra S L]
    {V : Type v} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    [Algebra R S] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L]
    [IsFractionRing R K] [FaithfulSMul S L] [Module.Flat R S] [NoZeroDivisors S]
    [FaithfulSMul R S] (M : Submodule R V) :
    Cardinal.lift.{v} (Module.rank S (spanBaseChange K S L M)) =
      Cardinal.lift.{max u v} (Module.rank R M) :=
  (IsBaseChange.of_equiv (f := ((spanBaseChangeEquiv K S L M).toLinearMap.restrictScalars R) ∘ₗ
    TensorProduct.mk R S M 1) (spanBaseChangeEquiv K S L M) (fun _ => rfl)).lift_rank_eq

theorem flat_spanBaseChange_inf_subspace.{u, v} {R : Type*} (K S : Type*) (L : Type u)
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Field K] [Field L]
    [Algebra R S] [FaithfulSMul R S] [Module.Flat R S]
    [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L]
    {V : Type v} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (M : Submodule R V) (W : Submodule K V) :
    spanBaseChange K S L (M ⊓ W.restrictScalars R) =
        spanBaseChange K S L M ⊓ (W.baseChange L).restrictScalars S ∧
      Cardinal.lift.{v} (Module.rank S (spanBaseChange K S L M)) =
        Cardinal.lift.{max u v} (Module.rank R M) ∧
      Cardinal.lift.{v} (Module.rank L (W.baseChange L)) =
        Cardinal.lift.{max u v} (Module.rank K W) ∧
      Module.finrank S (spanBaseChange K S L M) = Module.finrank R M ∧
      Module.finrank L (W.baseChange L) = Module.finrank K W :=
  ⟨spanBaseChange_inf_subspace K S L M W, lift_rank_spanBaseChange K S L M,
    lift_rank_baseChange L W, finrank_spanBaseChange K S L M, finrank_baseChange L W⟩

example (p : ℕ) [Fact p.Prime] (M : Submodule ℤ (Fin 2 → ℚ)) (W : Submodule ℚ (Fin 2 → ℚ)) :
    spanBaseChange ℚ ℤ_[p] ℚ_[p] (M ⊓ W.restrictScalars ℤ) =
      spanBaseChange ℚ ℤ_[p] ℚ_[p] M ⊓ (W.baseChange ℚ_[p]).restrictScalars ℤ_[p] :=
  (flat_spanBaseChange_inf_subspace ℚ ℤ_[p] ℚ_[p] M W).1

end GlobalTheory
