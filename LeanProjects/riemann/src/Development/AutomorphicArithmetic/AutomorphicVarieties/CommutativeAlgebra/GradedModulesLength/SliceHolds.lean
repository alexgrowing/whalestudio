import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.EtHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.FtHolds

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem exists_ptDer_eq_degree_smul_of_graded {O A K : Type} [CommRing O] [CommRing A] [Algebra O A] [Field K] [Algebra O K]
    (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (ξ : A →ₐ[O] K) :
    ∃ E ∈ PtDer ξ K, ∀ (j : ℤ) (a : A), a ∈ 𝒜 j → E a = (j : K) * ξ a := by
  classical
  let L : (DirectSum ℤ fun i => 𝒜 i) →ₗ[O] K :=
    DirectSum.toModule O ℤ K (fun i => ((i : ℤ) : K) • (ξ.toLinearMap ∘ₗ (𝒜 i).subtype))
  let E : A →ₗ[O] K := L ∘ₗ (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap
  have hE : ∀ (j : ℤ) (a : A), a ∈ 𝒜 j → E a = (j : K) * ξ a := by
    intro j a ha
    show L (DirectSum.decompose 𝒜 a) = _
    rw [DirectSum.decompose_of_mem 𝒜 ha, ← DirectSum.lof_eq_of O, DirectSum.toModule_lof]
    simp [smul_eq_mul]
  refine ⟨E, ?_, hE⟩
  intro a b
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous a =>
    induction b using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | homogeneous b =>
      rw [hE _ _ (SetLike.GradedMul.mul_mem a.2 b.2), hE _ _ a.2, hE _ _ b.2]
      simp only [map_mul, smul_eq_mul]
      push_cast
      ring
    | add b₁ b₂ h₁ h₂ =>
      simp only [mul_add, map_add, smul_add, h₁, h₂, smul_eq_mul]
      ring
  | add a₁ a₂ h₁ h₂ =>
    simp only [add_mul, map_add, smul_add, add_smul, h₁, h₂, smul_eq_mul]
    ring

private theorem degree_derivation_vanishes_on_homogeneous_ideal {O A K : Type} [CommRing O] [CommRing A] [Algebra O A] [Field K] [Algebra O K]
    (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (I : Ideal A) (hI : I.IsHomogeneous 𝒜) (ξ : A →ₐ[O] K)
    (hξ : OnS I ξ) (E : A →ₗ[O] K) (hE : ∀ (j : ℤ) (a : A), a ∈ 𝒜 j → E a = (j : K) * ξ a) :
    ∀ a ∈ I, E a = 0 := by
  classical
  intro a ha
  rw [← DirectSum.sum_support_decompose 𝒜 a, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hE i _ (SetLike.coe_mem _), hξ _ (hI i ha), mul_zero]

theorem UpperTheory.V.Alg.M.slice_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ I : Ideal A, I.IsHomogeneous 𝒜 → M2 𝒜 I → M4 𝒜 K I → ∀ f ∈ 𝒜 (-2), ∀ g ∈ 𝒜 2,
      {ξ : A →ₐ[O] K | OnS I ξ ∧ ξ f = 1 ∧ ξ g ≠ 0}.Finite ∧
      ∀ h : A, (∀ ξ : A →ₐ[O] K, OnS I ξ → ξ f = 1 → ξ g ≠ 0 → ξ h = 0) →
        ∃ (n : ℕ) (c : O), c ≠ 0 ∧ c • (g ^ n * h) ∈ I ⊔ Ideal.span {f - 1} := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x hx I hI h2 h4 f hf g hg
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective O K)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπ0 : π ≠ 0 := hπ.ne_zero
  set J : Ideal A := I ⊔ Ideal.span {f - 1} with hJ
  let s : A ⧸ J := algebraMap O (A ⧸ J) π * Ideal.Quotient.mk J g
  let C := Localization.Away s
  let φ : A →ₐ[O] C := (IsScalarTower.toAlgHom O (A ⧸ J) C).comp (Ideal.Quotient.mkₐ O J)
  have hφ : ∀ a, φ a = algebraMap (A ⧸ J) C (Ideal.Quotient.mk J a) := fun a => rfl
  have hφJ : ∀ a ∈ J, φ a = 0 := by
    intro a ha
    rw [hφ, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  have hf1 : φ f = 1 := by
    have h0 : φ (f - 1) = 0 := hφJ _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    rwa [map_sub, map_one, sub_eq_zero] at h0
  have hs_unit : IsUnit (algebraMap (A ⧸ J) C s) := IsLocalization.Away.algebraMap_isUnit s
  have hs_eq : algebraMap (A ⧸ J) C s = algebraMap O C π * φ g := by
    rw [hφ]
    simp only [s, map_mul]
    rw [← IsScalarTower.algebraMap_apply]
  rw [hs_eq] at hs_unit
  have hπu : IsUnit (algebraMap O C π) := isUnit_of_mul_isUnit_left hs_unit
  have hgu : IsUnit (φ g) := isUnit_of_mul_isUnit_right hs_unit
  have hunits : ∀ c : O, c ≠ 0 → IsUnit (algebraMap O C c) := by
    intro c hc
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hπ
    rw [map_mul, map_pow]
    exact (u.isUnit.map _).mul (hπu.pow n)
  haveI hft : Algebra.FiniteType O C := by
    have h1 : Algebra.FiniteType O (A ⧸ I) := (ft_holds O A 𝒜 x hx).2 I h2
    have h3 : Algebra.FiniteType O (A ⧸ J) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.factorₐ O (le_sup_left : I ≤ J))
        (Ideal.Quotient.factor_surjective (le_sup_left : I ≤ J))
    exact Algebra.FiniteType.trans h3 inferInstance
  have hslice : ∀ ψ : C →ₐ[O] K, OnS I (ψ.comp φ) ∧ (ψ.comp φ) f = 1 ∧ (ψ.comp φ) g ≠ 0 := by
    intro ψ
    refine ⟨fun a ha => ?_, ?_, ?_⟩
    · rw [AlgHom.comp_apply, hφJ a (Ideal.mem_sup_left ha), map_zero]
    · rw [AlgHom.comp_apply, hf1, map_one]
    · rw [AlgHom.comp_apply]
      exact (hgu.map ψ).ne_zero
  have hder : ∀ ψ : C →ₐ[O] K, PtDer ψ K = ⊥ := by
    intro ψ
    rw [eq_bot_iff]
    intro D hD
    rw [Submodule.mem_bot]
    obtain ⟨hOn, hξf, hξg⟩ := hslice ψ
    let D' : A →ₗ[O] K := D ∘ₗ φ.toLinearMap
    have hD' : D' ∈ PtDer (ψ.comp φ) K := by
      intro a b
      show D (φ (a * b)) = ψ (φ a) • D (φ b) + ψ (φ b) • D (φ a)
      rw [map_mul]
      exact hD _ _
    obtain ⟨E, hEm, hE⟩ := exists_ptDer_eq_degree_smul_of_graded 𝒜 (ψ.comp φ)
    have hEI := degree_derivation_vanishes_on_homogeneous_ideal 𝒜 I hI (ψ.comp φ) hOn E hE
    have hD'I : ∀ a ∈ I, D' a = 0 := by
      intro a ha
      show D (φ a) = 0
      rw [hφJ a (Ideal.mem_sup_left ha), map_zero]
    have htwo : TwoSigned 𝒜 (ψ.comp φ) := by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have h0 := h (-2) (by norm_num) f hf
        rw [hξf] at h0
        exact one_ne_zero h0
      · exact hξg (h 2 (by norm_num) g hg)
    obtain ⟨c, c', hcc, hlin⟩ := h4 (ψ.comp φ) hOn htwo D' hD' E hEm hD'I hEI
    have hD1 : D 1 = 0 := by
      have h0 := hD 1 1
      have hψ1 : ψ 1 = 1 := map_one ψ
      rw [mul_one, hψ1, one_smul] at h0
      have h5 : D 1 + D 1 = D 1 + 0 := by rw [add_zero]; exact h0.symm
      exact add_left_cancel h5
    have hD'f : D' f = 0 := by
      show D (φ f) = 0
      rw [hf1, hD1]
    have hEf : E f = -2 := by
      rw [hE (-2) f hf, hξf]
      norm_num
    have hc' : c' = 0 := by
      have h0 := LinearMap.congr_fun hlin f
      rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, hD'f, hEf,
        LinearMap.zero_apply, smul_zero, zero_add, smul_eq_mul] at h0
      have h6 : (-2 : K) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp h0).resolve_right h6
    have hc : c ≠ 0 := hcc.resolve_right (fun h => h hc')
    have hD0 : ∀ a, D (φ a) = 0 := by
      intro a
      have h0 := LinearMap.congr_fun hlin a
      rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, hc', zero_smul, add_zero,
        LinearMap.zero_apply, smul_eq_mul] at h0
      exact (mul_eq_zero.mp h0).resolve_left hc
    ext z
    obtain ⟨⟨b, t, ht⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) z
    obtain ⟨n, rfl⟩ := ht
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    set z := IsLocalization.mk' C (Ideal.Quotient.mk J a) (⟨s ^ n, n, rfl⟩ : Submonoid.powers s) with hz
    have hspec : z * algebraMap (A ⧸ J) C (s ^ n) = φ a := by
      rw [hz, IsLocalization.mk'_spec]
      rfl
    have ht : algebraMap (A ⧸ J) C (s ^ n) = φ ((algebraMap O A π * g) ^ n) := by
      rw [hφ]
      congr 1
    have htu : IsUnit (algebraMap (A ⧸ J) C (s ^ n)) := by
      rw [map_pow, hs_eq]
      exact hs_unit.pow n
    have h0 := hD z (algebraMap (A ⧸ J) C (s ^ n))
    rw [hspec, hD0, ht, hD0, smul_zero, zero_add, ← ht] at h0
    have hne : ψ (algebraMap (A ⧸ J) C (s ^ n)) ≠ 0 := (htu.map ψ).ne_zero
    rw [smul_eq_mul] at h0
    rw [LinearMap.zero_apply]
    exact ((mul_eq_zero.mp h0.symm).resolve_left hne)
  obtain ⟨hfin, hred⟩ := et_holds O K C hunits hder
  refine ⟨?_, ?_⟩
  · have hsub : {ξ : A →ₐ[O] K | OnS I ξ ∧ ξ f = 1 ∧ ξ g ≠ 0} ⊆
        Set.range (fun ψ : C →ₐ[O] K => ψ.comp φ) := by
      rintro ξ ⟨hOn, hξf, hξg⟩
      have hJξ : ∀ a ∈ J, ξ a = 0 := by
        have hle : J ≤ RingHom.ker ξ := by
          refine sup_le (fun a ha => hOn a ha) ?_
          rw [Ideal.span_le, Set.singleton_subset_iff]
          show ξ (f - 1) = 0
          rw [map_sub, hξf, map_one, sub_self]
        exact fun a ha => hle ha
      let ξB : (A ⧸ J) →ₐ[O] K := Ideal.Quotient.liftₐ J ξ hJξ
      have hu : ∀ y : Submonoid.powers s, IsUnit (ξB y) := by
        rintro ⟨_, n, rfl⟩
        rw [map_pow]
        refine IsUnit.pow n (isUnit_iff_ne_zero.mpr ?_)
        simp only [s, map_mul, AlgHom.commutes]
        refine mul_ne_zero ?_ ?_
        · exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective O K)).mpr hπ0
        · exact hξg
      refine ⟨IsLocalization.liftAlgHom (M := Submonoid.powers s) (S := C) hu, ?_⟩
      ext a
      show IsLocalization.liftAlgHom (M := Submonoid.powers s) (S := C) hu
        (algebraMap (A ⧸ J) C (Ideal.Quotient.mk J a)) = ξ a
      rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
      rfl
    exact (Set.finite_range _).subset hsub
  · intro h hh
    have hz : φ h = 0 := hred (φ h) (fun ψ => by
      obtain ⟨h1, h3, h5⟩ := hslice ψ
      exact hh _ h1 h3 h5)
    rw [hφ] at hz
    obtain ⟨⟨_, n, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers s) C _).mp hz
    refine ⟨n, π ^ n, pow_ne_zero _ hπ0, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have heq : Ideal.Quotient.mk J (π ^ n • (g ^ n * h)) = s ^ n * Ideal.Quotient.mk J h := by
      simp only [s, Algebra.smul_def, map_mul, map_pow, mul_pow]
      rw [Ideal.Quotient.mk_algebraMap]
      ring
    rw [heq]
    exact hm
