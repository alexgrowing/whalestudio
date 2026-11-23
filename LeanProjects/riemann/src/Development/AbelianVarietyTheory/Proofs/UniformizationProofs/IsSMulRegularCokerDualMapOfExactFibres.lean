import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AcyclicityLemmaDepthDifferentialCokernelsFiniteL
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndKerBaseChangeOfForallResidueField

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing TensorProduct Function

namespace GlobalTheory
namespace DualCokernel

variable {R : Type} [CommRing R]

theorem exists_smul_eq_zero_of_fibre (p : Ideal R) [hp : p.IsPrime] (N : Type) [AddCommGroup N]
    [Module R N] [Module.Finite R N] (h : Subsingleton (p.ResidueField ⊗[R] N)) :
    ∃ s, s ∉ p ∧ ∀ x : N, s • x = 0 := by
  have h1 : (⟨p, hp⟩ : PrimeSpectrum R) ∉ Module.support R N := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
    exact not_nontrivial_iff_subsingleton.mpr h
  rw [Module.mem_support_iff_of_finite] at h1
  obtain ⟨s, hs, hs'⟩ := Set.not_subset.mp h1
  exact ⟨s, hs', Module.mem_annihilator.mp hs⟩

theorem exists_homotopy_step (p : Ideal R) [hp : p.IsPrime] {M₀ M₁ M₂ M₃ : Type}
    [AddCommGroup M₀] [Module R M₀] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃] [Module.Finite R M₁] [Module.Projective R M₁]
    (a : M₀ →ₗ[R] M₁) (b : M₁ →ₗ[R] M₂) (c : M₂ →ₗ[R] M₃) (hab : ∀ x, b (a x) = 0)
    (hbc : ∀ x, c (b x) = 0)
    (hex : Exact (a.lTensor p.ResidueField) (b.lTensor p.ResidueField))
    (s : R) (hs : s ∉ p) (h₁ : M₂ →ₗ[R] M₁) (h₂ : M₃ →ₗ[R] M₂)
    (hh : ∀ x, b (h₁ x) + h₂ (c x) = s • x) :
    ∃ (t : R) (_ : t ∉ p) (k₀ : M₁ →ₗ[R] M₀) (k₁ : M₂ →ₗ[R] M₁),
      ∀ x, a (k₀ x) + k₁ (b x) = t • x := by
  have hb : ∀ x, b (h₁ (b x)) = s • b x := fun x => by simpa [hbc] using hh (b x)
  set π : M₁ →ₗ[R] M₁ := s • LinearMap.id - h₁ ∘ₗ b with hπ
  have hbπ : b ∘ₗ π = 0 := by
    ext x
    simp [hπ, hb]
  set N := LinearMap.range a ⊔ LinearMap.range (h₁ ∘ₗ b) with hN
  have hsub : Subsingleton (p.ResidueField ⊗[R] (M₁ ⧸ N)) := by
    refine subsingleton_of_forall_eq 0 fun y => ?_
    obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective p.ResidueField N.mkQ_surjective y
    have h1 : b.lTensor p.ResidueField (π.lTensor p.ResidueField x) = 0 := by
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hbπ]
      simp
    obtain ⟨z, hz⟩ := (hex _).1 h1
    have h2 : N.mkQ ∘ₗ a = 0 := by
      ext w
      exact (Submodule.Quotient.mk_eq_zero N).2 (Submodule.mem_sup_left ⟨w, rfl⟩)
    have h3 : N.mkQ ∘ₗ π = s • N.mkQ := by
      ext w
      have : N.mkQ (h₁ (b w)) = 0 :=
        (Submodule.Quotient.mk_eq_zero N).2 (Submodule.mem_sup_right ⟨w, rfl⟩)
      simp only [hπ, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, map_sub, this, sub_zero, map_smul]
    have h4 := congrArg (N.mkQ.lTensor p.ResidueField) hz
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h2, ← LinearMap.comp_apply,
      ← LinearMap.lTensor_comp, h3, LinearMap.lTensor_zero, LinearMap.zero_apply,
      LinearMap.lTensor_smul, LinearMap.smul_apply, ← algebraMap_smul p.ResidueField] at h4
    exact (smul_eq_zero.mp h4.symm).resolve_left
      (fun h0 => hs (Ideal.algebraMap_residueField_eq_zero.mp h0))
  obtain ⟨t, ht, htN⟩ := exists_smul_eq_zero_of_fibre p (M₁ ⧸ N) hsub
  have hmem : ∀ x, (t • π) x ∈ LinearMap.range a := by
    intro x
    have h1 : t • x ∈ N := (Submodule.Quotient.mk_eq_zero N).1 (htN (N.mkQ x))
    obtain ⟨_, ⟨u, rfl⟩, _, ⟨v, rfl⟩, huv⟩ := Submodule.mem_sup.mp h1
    rw [LinearMap.smul_apply, ← map_smul, ← huv]
    refine ⟨s • u, ?_⟩
    simp [hπ, hab, hb]
  obtain ⟨k, hk⟩ := Module.projective_lifting_property a.rangeRestrict
    (LinearMap.codRestrict _ _ hmem) a.surjective_rangeRestrict
  refine ⟨t * s, fun h => (hp.mem_or_mem h).elim ht hs, k, t • h₁, fun x => ?_⟩
  have : a (k x) = (t • π) x := congrArg Subtype.val (LinearMap.congr_fun hk x)
  simp [this, hπ, smul_sub, mul_smul]

section Depth

variable [IsLocalRing R]

abbrev ExtZero (M : Type) [AddCommGroup M] [Module R M] (n : ℕ) : Prop :=
  Subsingleton (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R M) n)

theorem extZero_coker {X F : Type} [AddCommGroup X] [Module R X] [AddCommGroup F] [Module R F]
    {Y : Type} [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] F) (q : F →ₗ[R] Y) (hf : Injective f)
    (hq : Surjective q) (hex : Exact f q) (n : ℕ) (hX : ExtZero (R := R) X (n + 1))
    (hF : ExtZero (R := R) F n) : ExtZero (R := R) Y n := by
  have hS : (ModuleCat.shortComplexOfCompEqZero f q hex.linearMap_comp_eq_zero).ShortExact :=
    ModuleCat.shortComplex_shortExact _ hex hf hq
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₃ _ hS x rfl (@Subsingleton.elim _ hX _ _)
  rw [@Subsingleton.elim _ hF y 0]
  exact Ext.zero_comp _ _ _ _ _

theorem extZero_retract {X F : Type} [AddCommGroup X] [Module R X] [AddCommGroup F] [Module R F]
    (f : X →ₗ[R] F) (q : F →ₗ[R] X) (h : q ∘ₗ f = LinearMap.id) (n : ℕ)
    (hF : ExtZero (R := R) F n) : ExtZero (R := R) X n := by
  have hid : 𝟙 (ModuleCat.of R X) = ModuleCat.ofHom f ≫ ModuleCat.ofHom q := by
    rw [← ModuleCat.ofHom_comp, h, ModuleCat.ofHom_id]
  refine subsingleton_of_forall_eq 0 fun x => ?_
  rw [← Ext.comp_mk₀_id x, hid, ← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_second_deg_zero,
    @Subsingleton.elim _ hF (x.comp _ _) 0, Ext.zero_comp]

variable [IsNoetherianRing R]

theorem eq_zero_of_extZero {M : Type} [AddCommGroup M] [Module R M] (h : ExtZero (R := R) M 0)
    (x : M) (hx : ∀ p : Ideal R, p.IsPrime → p ≠ maximalIdeal R → ∃ s, s ∉ p ∧ s • x = 0) :
    x = 0 := by
  by_contra h0
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R x h0
  by_cases hm : P = maximalIdeal R
  · subst hm
    obtain ⟨-, f, hf⟩ := (isAssociatedPrime_iff_exists_injective_linearMap _ _).1 hP
    have h1 : Subsingleton (ModuleCat.of R (R ⧸ maximalIdeal R) ⟶ ModuleCat.of R M) :=
      Ext.addEquiv₀.subsingleton_congr.mp h
    have h2 : f = 0 := congrArg ModuleCat.Hom.hom (h1.elim (ModuleCat.ofHom f) 0)
    have : Nontrivial (R ⧸ maximalIdeal R) := Ideal.Quotient.nontrivial_iff.mpr
      (maximalIdeal.isMaximal R).ne_top
    exact one_ne_zero (hf (a₁ := 1) (a₂ := 0) (by simp [h2]))
  · obtain ⟨s, hs, hsx⟩ := hx P hP.isPrime hm
    exact hs (hle (by simpa [Submodule.mem_colon_singleton] using hsx))

theorem coker_step (ϖ : R) (hϖ : ϖ ∈ maximalIdeal R) {D₀ D₁ D₂ : Type}
    [AddCommGroup D₀] [Module R D₀] [AddCommGroup D₁] [Module R D₁] [AddCommGroup D₂] [Module R D₂]
    [Module.Finite R D₁] (β : D₂ →ₗ[R] D₁) (α : D₁ →ₗ[R] D₀) (hαβ : ∀ x, α (β x) = 0)
    (hD₀ : IsSMulRegular D₀ ϖ) (n : ℕ) (hE₀ : ∀ j < n + 1, ExtZero (R := R) D₀ j)
    (hQ : IsSMulRegular (D₁ ⧸ LinearMap.range β) ϖ)
    (hE : ∀ j < n + 2, ExtZero (R := R) (D₁ ⧸ LinearMap.range β) j)
    (h₁ : ∀ p : Ideal R, p.IsPrime → ϖ ∈ p → p ≠ maximalIdeal R →
      ∃ s, s ∉ p ∧ ∀ x, α x = 0 → s • x ∈ LinearMap.range β)
    (h₀ : ∀ p : Ideal R, p.IsPrime → ϖ ∈ p → p ≠ maximalIdeal R →
      ∃ s, s ∉ p ∧ ∀ x, ϖ • x ∈ LinearMap.range α → s • x ∈ LinearMap.range α) :
    IsSMulRegular (D₀ ⧸ LinearMap.range α) ϖ ∧
      ∀ j < n + 1, ExtZero (R := R) (D₀ ⧸ LinearMap.range α) j := by
  let μ : (D₁ ⧸ LinearMap.range β) →ₗ[R] (D₁ ⧸ LinearMap.range β) := ϖ • LinearMap.id
  have hμ : ExtZero (R := R) ((D₁ ⧸ LinearMap.range β) ⧸ LinearMap.range μ) 0 :=
    extZero_coker μ _ hQ (Submodule.mkQ_surjective _) μ.exact_map_mkQ_range 0
      (hE 1 (by omega)) (hE 0 (by omega))
  have hker : LinearMap.ker α ≤ LinearMap.range β := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal R)
      (IsNoetherian.noetherian _) (maximalIdeal_le_jacobson _) fun x hx => ?_
    have h1 := eq_zero_of_extZero hμ
      ((LinearMap.range μ).mkQ ((LinearMap.range β).mkQ x)) fun p hp hm => by
        by_cases hϖp : ϖ ∈ p
        · obtain ⟨s, hs, hs'⟩ := h₁ p hp hϖp hm
          refine ⟨s, hs, ?_⟩
          rw [← map_smul, ← map_smul, Submodule.mkQ_apply (LinearMap.range β),
            (Submodule.Quotient.mk_eq_zero _).2 (hs' x hx), map_zero]
        · refine ⟨ϖ, hϖp, ?_⟩
          rw [← map_smul]
          exact (Submodule.Quotient.mk_eq_zero _).2 ⟨_, rfl⟩
    obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero _).1 h1
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ z
    obtain ⟨y, hy⟩ : ϖ • z - x ∈ LinearMap.range β := (Submodule.Quotient.eq _).1 hz
    have hz0 : α z = 0 := by
      have := hαβ y
      rw [hy, map_sub, LinearMap.mem_ker.mp hx, sub_zero, map_smul] at this
      exact hD₀ (this.trans (smul_zero ϖ).symm)
    have : x = -β y + ϖ • z := by rw [hy]; abel
    rw [this]
    exact Submodule.add_mem_sup (neg_mem ⟨y, rfl⟩) (Submodule.smul_mem_smul hϖ hz0)
  have hle : LinearMap.range β ≤ LinearMap.ker α := by
    rintro _ ⟨y, rfl⟩
    exact hαβ y
  have hE' : ∀ j < n + 1, ExtZero (R := R) (D₀ ⧸ LinearMap.range α) j := fun j hj =>
    extZero_coker ((LinearMap.range β).liftQ α hle) (LinearMap.range α).mkQ
      (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ hker))
      (Submodule.mkQ_surjective _)
      (by rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_liftQ]) j
      (hE _ (by omega)) (hE₀ j hj)
  refine ⟨IsSMulRegular.of_right_eq_zero_of_smul fun x hx => ?_, hE'⟩
  refine eq_zero_of_extZero (hE' 0 (by omega)) x fun p hp hm => ?_
  by_cases hϖp : ϖ ∈ p
  · obtain ⟨s, hs, hs'⟩ := h₀ p hp hϖp hm
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    exact ⟨s, hs, (Submodule.Quotient.mk_eq_zero _).2
      (hs' x ((Submodule.Quotient.mk_eq_zero _).1 hx))⟩
  · exact ⟨ϖ, hϖp, hx⟩

theorem extZero_self (ϖ : R) (g : ℕ) (hϖ : ϖ ∈ nonZeroDivisors R) (hm : ϖ ∈ maximalIdeal R)
    [IsRegularLocalRing (R ⧸ Ideal.span {ϖ})] (hg : ringKrullDim (R ⧸ Ideal.span {ϖ}) = g)
    (j : ℕ) (hj : j < g + 1) : ExtZero (R := R) R j := by
  obtain ⟨xs, h, hd⟩ := exists_ofList_eq_maximalIdeal_length_eq (R ⧸ Ideal.span {ϖ})
  have hreg := isRegular_of_ofList_eq_maximalIdeal h hd.le
  have hlen : xs.length = g := by
    rw [hg] at hd
    exact_mod_cast hd
  let σ := Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {ϖ}))
  have hσ : ∀ a, Ideal.Quotient.mk _ (σ a) = a := Function.surjInv_eq _
  have hmap : (xs.map σ).map (algebraMap R (R ⧸ Ideal.span {ϖ})) = xs := by
    rw [List.map_map]
    exact List.map_id'' hσ xs
  have h1 : RingTheory.Sequence.IsRegular (R ⧸ Ideal.span {ϖ}) (xs.map σ) := by
    rw [← hmap] at hreg
    exact ((AddEquiv.refl _).isRegular_congr <| List.forall₂_map_left_iff.mpr <|
      List.forall₂_same.mpr fun r _ => algebraMap_smul _ r).1 hreg
  have e : QuotSMulTop ϖ R ≃ₗ[R] R ⧸ Ideal.span {ϖ} :=
    Submodule.quotEquivOfEq _ _ (by
      rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top])
  have h2 : RingTheory.Sequence.IsRegular R (ϖ :: xs.map σ) := by
    rw [RingTheory.Sequence.isRegular_cons_iff, e.isRegular_congr]
    exact ⟨(isRegular_iff_mem_nonZeroDivisors.mpr hϖ).left.isSMulRegular, h1⟩
  refine ModuleCat.subsingleton_ext_of_exists_isRegular (maximalIdeal R) _ ?_ _ ?_ _ ?_ h2 j
    (by simpa [hlen] using hj)
  · rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
  · rw [smul_eq_mul, Ideal.mul_top]
    exact (maximalIdeal.isMaximal R).ne_top.lt_top
  · intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hm
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
      have hx' : x ∈ maximalIdeal _ := h ▸ Ideal.subset_span hx
      rw [mem_maximalIdeal, mem_nonunits_iff] at hx' ⊢
      exact fun hu => hx' (hσ x ▸ hu.map (Ideal.Quotient.mk _))

end Depth

section Complex

variable (C : CochainComplex (ModuleCat.{0} R) ℕ)

theorem d_d_apply (i j k : ℕ) (x : C.X i) : (C.d j k).hom ((C.d i j).hom x) = 0 := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, C.d_comp_d]
  rfl

theorem exact_fibre (p : Ideal R) [p.IsPrime] {K : Type} [Field K] (φ : R →+* K)
    (hφ : RingHom.ker φ = p) (i : ℕ)
    (h : (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) :
    Exact ((C.d (i - 1) i).hom.lTensor p.ResidueField)
      ((C.d i (i + 1)).hom.lTensor p.ResidueField) := by
  let := φ.toAlgebra
  rw [← exact_lTensor_iff_residueField p K hφ,
    ← isZero_homology_extendScalars_iff K C (by cases i <;> simp) (by simp),
    ← HomologicalComplex.exactAt_iff_isZero_homology]
  exact h

theorem exists_homotopy (hF : ∀ i, Module.Free R (C.X i) ∧ Module.Finite R (C.X i))
    (n : ℕ) (hn : ∀ i, n < i → IsZero (C.X i)) (p : Ideal R) [hp : p.IsPrime]
    (h : ∀ i, Exact ((C.d (i - 1) i).hom.lTensor p.ResidueField)
      ((C.d i (i + 1)).hom.lTensor p.ResidueField)) (i : ℕ) :
    ∃ (t : R) (_ : t ∉ p) (k₀ : C.X i →ₗ[R] C.X (i - 1)) (k₁ : C.X (i + 1) →ₗ[R] C.X i),
      ∀ x, (C.d (i - 1) i).hom (k₀ x) + k₁ ((C.d i (i + 1)).hom x) = t • x := by
  induction hk : n + 1 - i generalizing i with
  | zero =>
    have := ModuleCat.subsingleton_of_isZero (hn i (by omega))
    exact ⟨1, (Ideal.ne_top_iff_one p).1 hp.ne_top, 0, 0, fun x => Subsingleton.elim _ _⟩
  | succ k ih =>
    obtain ⟨s, hs, h₁, h₂, hh⟩ := ih (i + 1) (by omega)
    have := (hF i).1
    have := (hF i).2
    exact exists_homotopy_step p _ _ _ (d_d_apply C _ _ _) (d_d_apply C _ _ _) (h i) s hs h₁ h₂ hh

end Complex

end DualCokernel

open DualCokernel in

theorem isSMulRegular_coker_dualMap_of_exact_fibres :
    ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (ϖ : A) (g : ℕ),
      ϖ ∈ nonZeroDivisors A → IsRegularLocalRing (A ⧸ Ideal.span {ϖ}) →
      ringKrullDim (A ⧸ Ideal.span {ϖ}) = g → ∀ C : CochainComplex (ModuleCat.{0} A) ℕ,
      (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i)) → (∃ n, ∀ i, n < i → IsZero (C.X i)) →
      (∀ p : PrimeSpectrum A, ϖ ∈ p.asIdeal → ∃ (K : Type) (_ : Field K) (φ : A →+* K),
        RingHom.ker φ = p.asIdeal ∧ ∀ i, (p.asIdeal ≠ IsLocalRing.maximalIdeal A ∨ g < i) →
          (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) →
      IsSMulRegular (Module.Dual A (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ϖ := by
  intro A _ _ _ ϖ g hϖ hreg hg C hF ⟨n, hn⟩ hex
  have hfree := fun i => (hF i).1
  have hfin := fun i => (hF i).2
  have hm : ϖ ∈ maximalIdeal A := by
    refine le_maximalIdeal (Ideal.Quotient.nontrivial_iff.mp inferInstance)
      (Ideal.mem_span_singleton_self ϖ)
  have hDreg : ∀ i, IsSMulRegular (Module.Dual A (C.X i)) ϖ := fun i =>
    IsSMulRegular.of_right_eq_zero_of_smul fun f hf => LinearMap.ext fun x =>
      (mem_nonZeroDivisors_iff.mp hϖ).1 _ (LinearMap.congr_fun hf x)
  have hDext : ∀ i, ∀ j < g + 1, ExtZero (R := A) (Module.Dual A (C.X i)) j := fun i j hj =>
    FiniteLengthComplex.subsingleton_ext_free _ j (extZero_self ϖ g hϖ hm hg j hj) _
  have hdd : ∀ i j k f, (C.d i j).hom.dualMap ((C.d j k).hom.dualMap f) = 0 := fun i j k f => by
    ext x
    simp [d_d_apply]

  have hloc : ∀ i, ∀ p : Ideal A, p.IsPrime → ϖ ∈ p → p ≠ maximalIdeal A → ∃ s, s ∉ p ∧
      ∀ f, (C.d (i - 1) i).hom.dualMap f = 0 →
        s • f ∈ LinearMap.range (C.d i (i + 1)).hom.dualMap := by
    intro i p hp hϖp hpm
    obtain ⟨K, _, φ, hφ, hK⟩ := hex ⟨p, hp⟩ hϖp
    obtain ⟨t, ht, k₀, k₁, hk⟩ := exists_homotopy C hF n hn p
      (fun j => exact_fibre C p φ hφ j (hK j (Or.inl hpm))) i
    refine ⟨t, ht, fun f hf => ⟨k₁.dualMap f, LinearMap.ext fun x => ?_⟩⟩
    have h1 : f ((C.d (i - 1) i).hom (k₀ x)) = 0 := LinearMap.congr_fun hf (k₀ x)
    have h2 := congrArg f (hk x)
    rw [map_add, h1, zero_add, map_smul] at h2
    exact h2
  have key : ∀ k i, i + k = g →
      IsSMulRegular (Module.Dual A (C.X i) ⧸ LinearMap.range (C.d i (i + 1)).hom.dualMap) ϖ ∧
      ∀ j < i + 1, ExtZero (R := A)
        (Module.Dual A (C.X i) ⧸ LinearMap.range (C.d i (i + 1)).hom.dualMap) j := by
    intro k
    induction k with
    | zero =>
      rintro i rfl
      obtain ⟨K, _, φ, hφ, hK⟩ := hex ⟨maximalIdeal A, inferInstance⟩ hm
      obtain ⟨s, t, hst⟩ := exists_homotopy_of_forall_exact_residueField
        (f := (C.d i (i + 1)).hom) (g := (C.d (i + 1) (i + 1 + 1)).hom)
        (LinearMap.ext (d_d_apply C _ _ _)) fun m hm' => by
          exact exact_fibre C m φ (hφ.trans (eq_maximalIdeal hm').symm) (i + 1)
            (hK _ (Or.inr (by omega)))
      have hds : ∀ x, (C.d i (i + 1)).hom (s ((C.d i (i + 1)).hom x)) = (C.d i (i + 1)).hom x :=
        fun x => by simpa [d_d_apply] using LinearMap.congr_fun hst ((C.d i (i + 1)).hom x)
      let ι := (LinearMap.range (C.d i (i + 1)).hom.dualMap).liftQ
        (LinearMap.id - (C.d i (i + 1)).hom.dualMap ∘ₗ s.dualMap) (by
          rintro _ ⟨f, rfl⟩
          ext x
          simp [hds])
      have hι : (LinearMap.range (C.d i (i + 1)).hom.dualMap).mkQ ∘ₗ ι = LinearMap.id := by
        refine Submodule.linearMap_qext _ (LinearMap.ext fun f => ?_)
        refine (Submodule.Quotient.eq _).2 ⟨-s.dualMap f, ?_⟩
        simp [ι]
      have hinj : Injective ι := HasLeftInverse.injective ⟨_, LinearMap.congr_fun hι⟩
      exact ⟨(hDreg i).of_injective ι hinj,
        fun j hj => extZero_retract ι _ hι j (hDext i j hj)⟩
    | succ k ih =>
      intro i hi
      obtain ⟨h1, h2⟩ := ih (i + 1) (by omega)
      refine coker_step ϖ hm _ _ (hdd _ _ _) (hDreg i) i (fun j hj => hDext i j (by omega)) h1 h2
        (hloc (i + 1)) fun p hp hϖp hpm => ?_
      obtain ⟨s, hs, hs'⟩ := hloc i p hp hϖp hpm
      refine ⟨s, hs, fun f ⟨y, hy⟩ => hs' f (hDreg _ ?_)⟩
      have := hdd (i - 1) i (i + 1) y
      rw [hy, map_smul] at this
      exact this.trans (smul_zero ϖ).symm
  exact (key g 0 (zero_add g)).1

end GlobalTheory
