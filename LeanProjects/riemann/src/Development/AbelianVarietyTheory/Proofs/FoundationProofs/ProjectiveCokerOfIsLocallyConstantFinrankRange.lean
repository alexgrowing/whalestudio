import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapSpanBaseChangeEquivSubmoduleOf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ProjectiveOfIsLocallyConstantFinrankFiber

open TensorProduct Module Function Filter Topology

namespace GlobalTheory

open Semicont

section FiniteModule

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem exists_away_equiv_of_eventually_finrank_fiber_eq [IsReduced R] [Module.Finite R M]
    (p : PrimeSpectrum R)
    (h : ∀ᶠ q : PrimeSpectrum R in 𝓝 p,
      finrank q.asIdeal.ResidueField (q.asIdeal.ResidueField ⊗[R] M) =
        finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M)) :
    ∃ f ∉ p.asIdeal, Nonempty
      ((Fin (finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M)) →
        Localization.Away f) ≃ₗ[Localization.Away f] LocalizedModule.Away f M) := by
  obtain ⟨φ, hφ⟩ := exists_baseChange_surjective (R := R) (M := M) p.asIdeal.ResidueField
  have h1 := h.and ((isOpen_setOf_baseChange_surjective φ).mem_nhds hφ)
  obtain ⟨_, ⟨f, rfl⟩, hpf, hf⟩ := (PrimeSpectrum.isTopologicalBasis_basic_opens.mem_nhds_iff).1 h1
  have hker : ∀ x, φ x = 0 → f • x = 0 := by
    intro x hx
    ext j
    refine IsReduced.eq_zero _ (nilpotent_iff_mem_prime.2 fun J hJ => ?_)
    by_cases hfJ : f ∈ J
    · exact J.mul_mem_right _ hfJ
    obtain ⟨h2, h3⟩ := hf (show (⟨J, hJ⟩ : PrimeSpectrum R) ∈ _ from hfJ)
    have hinj : Injective (φ.baseChange J.ResidueField) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        ((finrank_baseChange_fin _ _).trans h2.symm)).2 h3
    have h4 : (1 : J.ResidueField) ⊗ₜ[R] x = 0 := hinj (by simp [hx])
    have h5 :=
      congrFun (congrArg (TensorProduct.piScalarRight R J.ResidueField J.ResidueField _) h4) j
    refine J.mul_mem_left _ ?_
    rw [← Ideal.algebraMap_residueField_eq_zero]
    simpa [Algebra.smul_def] using h5
  let A := Localization.Away f
  have hsurj : Surjective (φ.baseChange A) := by
    rw [baseChange_surjective_iff]
    have : Subsingleton (LocalizedModule.Away f (M ⧸ LinearMap.range φ)) := by
      rw [LocalizedModule.subsingleton_iff_disjoint, Set.disjoint_left]
      intro q hq
      have h3 : Surjective (φ.baseChange q.asIdeal.ResidueField) := (hf hq).2
      rwa [baseChange_surjective_iff, ← not_nontrivial_iff_subsingleton,
        ← Module.mem_support_iff_nontrivial_residueField_tensorProduct] at h3
    exact (LocalizedModule.equivTensorProduct (Submonoid.powers f) _).symm.toEquiv.subsingleton
  have hinj : Injective (φ.baseChange A) := by
    have : Module.Flat R A := IsLocalization.flat A (Submonoid.powers f)
    rw [← LinearMap.ker_eq_bot, ← baseChange_ker, Submodule.baseChange_eq_span, eq_bot_iff,
      Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hu : IsUnit (algebraMap R A f) := IsLocalization.Away.algebraMap_isUnit f
    refine (hu.smul_eq_zero).1 ?_
    rw [algebraMap_smul, ← map_smul, hker x hx, map_zero]
  exact ⟨f, hpf, ⟨(TensorProduct.piScalarRight R A A _).symm ≪≫ₗ
    LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩ ≪≫ₗ
    (LocalizedModule.equivTensorProduct (Submonoid.powers f) M).symm⟩⟩

theorem finitePresentation_of_isLocallyConstant_finrank_fiber [IsReduced R] [Module.Finite R M]
    (h : IsLocallyConstant fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M)) :
    Module.FinitePresentation R M := by
  refine Module.FinitePresentation.of_localizationSpan
    {f | Module.FinitePresentation (Localization.Away f) (LocalizedModule.Away f M)} ?_
    fun g => g.2
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨f, hf, ⟨e⟩⟩ := exists_away_equiv_of_eventually_finrank_fiber_eq (M := M)
    ⟨m, hm.isPrime⟩ (h.eventually_eq _)
  exact hf (hle (Ideal.subset_span (Module.FinitePresentation.of_equiv e)))

theorem projective_of_finite_of_isLocallyConstant_finrank_fiber [IsReduced R] [Module.Finite R M]
    (h : IsLocallyConstant fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M)) :
    Module.Projective R M :=
  have := finitePresentation_of_isLocallyConstant_finrank_fiber h
  projective_of_isLocallyConstant_finrank_fiber h

theorem projective_of_finite_of_finrank_fiber_eq [IsReduced R] [Module.Finite R M] (ρ : ℕ)
    (h : ∀ p : PrimeSpectrum R,
      finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M) = ρ) :
    Module.Projective R M ∧ ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = ρ := by
  have : Module.Projective R M := projective_of_finite_of_isLocallyConstant_finrank_fiber
    (IsLocallyConstant.of_constant _ fun p q => (h p).trans (h q).symm)
  exact ⟨this, fun p => (Module.rankAtStalk_eq p).trans (h p)⟩

theorem finrank_tensorProduct_eq_finrank_fiber (k : Type*) [Field k] [Algebra R k]
    (p : PrimeSpectrum R) (hp : p.asIdeal = RingHom.ker (algebraMap R k)) :
    finrank k (k ⊗[R] M) = finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M) := by
  letI : Algebra p.asIdeal.ResidueField k :=
    (Ideal.ResidueField.lift p.asIdeal (algebraMap R k) hp.le (fun x hx => by
      refine IsUnit.mk0 _ fun h0 => hx ?_
      rw [hp]
      exact h0)).toAlgebra
  have : IsScalarTower R p.asIdeal.ResidueField k :=
    IsScalarTower.of_algebraMap_eq fun x => (Ideal.ResidueField.lift_algebraMap ..).symm
  rw [← (AlgebraTensorModule.cancelBaseChange R p.asIdeal.ResidueField k k M).finrank_eq,
    Module.finrank_baseChange]

end FiniteModule

section Map

variable {R : Type*} [CommRing R] {E F : Type*} [AddCommGroup E] [Module R E]
  [AddCommGroup F] [Module R F]

theorem finrank_baseChange_coker_add_finrank_range [Module.Finite R F]
    (k : Type*) [Field k] [Algebra R k] (φ : E →ₗ[R] F) :
    finrank k (k ⊗[R] (F ⧸ LinearMap.range φ)) + finrank k (LinearMap.range (φ.baseChange k)) =
      finrank k (k ⊗[R] F) := by
  rw [(baseChangeQuotEquiv k _).finrank_eq, baseChange_range]
  exact Submodule.finrank_quotient_add_finrank _

theorem projective_coker_of_isLocallyConstant_finrank_range [IsReduced R]
    [Module.Finite R F] [Module.Projective R F] (φ : E →ₗ[R] F)
    (h : IsLocallyConstant fun p : PrimeSpectrum R => finrank p.asIdeal.ResidueField
      (LinearMap.range (φ.baseChange p.asIdeal.ResidueField))) :
    Module.Projective R (F ⧸ LinearMap.range φ) := by
  refine projective_of_finite_of_isLocallyConstant_finrank_fiber
    ((IsLocallyConstant.iff_eventually_eq _).2 fun p => ?_)
  filter_upwards [h.eventually_eq p, (isLocallyConstant_finrank_fiber F).eventually_eq p]
    with q h1 h2
  have h3 := finrank_baseChange_coker_add_finrank_range p.asIdeal.ResidueField φ
  have h4 := finrank_baseChange_coker_add_finrank_range q.asIdeal.ResidueField φ
  omega

theorem exists_comp_comp_eq_of_isLocallyConstant_finrank_range [IsReduced R]
    [Module.Finite R F] [Module.Projective R F] (φ : E →ₗ[R] F)
    (h : IsLocallyConstant fun p : PrimeSpectrum R => finrank p.asIdeal.ResidueField
      (LinearMap.range (φ.baseChange p.asIdeal.ResidueField))) :
    ∃ s : F →ₗ[R] E, φ ∘ₗ s ∘ₗ φ = φ :=
  have := projective_coker_of_isLocallyConstant_finrank_range φ h
  exists_comp_comp_eq_of_projective φ

theorem exists_retraction_range_of_generalizedInverse (φ : E →ₗ[R] F) (s : F →ₗ[R] E)
    (hs : φ ∘ₗ s ∘ₗ φ = φ) :
    ∃ r : F →ₗ[R] LinearMap.range φ, r ∘ₗ (LinearMap.range φ).subtype = LinearMap.id := by
  refine ⟨φ.rangeRestrict ∘ₗ s, LinearMap.ext ?_⟩
  rintro ⟨_, x, rfl⟩
  exact Subtype.ext (LinearMap.congr_fun hs x)

theorem exists_retraction_ker_of_generalizedInverse (φ : E →ₗ[R] F) (s : F →ₗ[R] E)
    (hs : φ ∘ₗ s ∘ₗ φ = φ) :
    ∃ r : E →ₗ[R] LinearMap.ker φ, r ∘ₗ (LinearMap.ker φ).subtype = LinearMap.id := by
  have hs' : ∀ x, φ (s (φ x)) = φ x := LinearMap.congr_fun hs
  refine ⟨(LinearMap.id - s ∘ₗ φ).codRestrict _ fun x => by simp [hs'], ?_⟩
  ext x
  simp

theorem lTensor_subtype_injective_of_retraction (P : Submodule R E) (r : E →ₗ[R] P)
    (hr : r ∘ₗ P.subtype = LinearMap.id) (N : Type*) [AddCommGroup N] [Module R N] :
    Injective (P.subtype.lTensor N) :=
  LeftInverse.injective (g := r.lTensor N) fun x => by
    rw [← LinearMap.lTensor_comp_apply, hr, LinearMap.lTensor_id, LinearMap.id_apply]

theorem baseChange_ker_of_comp_comp_eq (φ : E →ₗ[R] F) (s : F →ₗ[R] E)
    (hs : φ ∘ₗ s ∘ₗ φ = φ) (S : Type*) [CommRing S] [Algebra R S] :
    (LinearMap.ker φ).baseChange S = LinearMap.ker (φ.baseChange S) := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      LinearMap.comp_ker_subtype, LinearMap.baseChange_zero, LinearMap.zero_apply]
  · intro hz
    obtain ⟨y, hy⟩ := (tensorKer_bijective_of_comp_comp_eq S S φ s hs).2 ⟨z, hz⟩
    exact ⟨y, (LinearMap.tensorKer_coe S S φ y).symm.trans (congrArg Subtype.val hy)⟩

theorem finrank_baseChange_eq_of_injective (P : Submodule R E) (k : Type*) [Field k] [Algebra R k]
    (h : Injective (P.subtype.lTensor k)) :
    finrank k (k ⊗[R] P) = finrank k (P.baseChange k) :=
  (LinearEquiv.ofInjective (P.subtype.baseChange k) h).finrank_eq

universe u v

theorem finite_projective_of_isLocallyConstant_finrank_range [IsReduced R]
    [Module.Finite R E] [Module.Projective R E] [Module.Finite R F] [Module.Projective R F]
    (φ : E →ₗ[R] F)
    (h : IsLocallyConstant fun p : PrimeSpectrum R => finrank p.asIdeal.ResidueField
      (LinearMap.range (φ.baseChange p.asIdeal.ResidueField))) :
    (Module.Finite R (LinearMap.range φ) ∧ Module.Projective R (LinearMap.range φ)) ∧
    (Module.Finite R (LinearMap.ker φ) ∧ Module.Projective R (LinearMap.ker φ)) ∧
    (Module.Finite R (F ⧸ LinearMap.range φ) ∧ Module.Projective R (F ⧸ LinearMap.range φ)) ∧
    (∃ P : Submodule R E, IsCompl (LinearMap.ker φ) P) ∧
    (∃ Q : Submodule R F, IsCompl (LinearMap.range φ) Q) ∧
    (∀ p : PrimeSpectrum R, Module.rankAtStalk (LinearMap.range φ) p =
      finrank p.asIdeal.ResidueField (LinearMap.range (φ.baseChange p.asIdeal.ResidueField))) ∧
    (∀ p : PrimeSpectrum R, Module.rankAtStalk (LinearMap.ker φ) p =
      finrank p.asIdeal.ResidueField (LinearMap.ker (φ.baseChange p.asIdeal.ResidueField))) ∧
    (∀ (S : Type u) (N : Type v) [CommRing S] [Algebra R S] [AddCommGroup N] [Module R N]
      [Module S N] [IsScalarTower R S N], Bijective (LinearMap.tensorKer S N φ) ∧
        Injective ((LinearMap.range φ).subtype.lTensor N)) ∧
    ∀ (S : Type u) [CommRing S] [Algebra R S],
      (LinearMap.ker φ).baseChange S = LinearMap.ker (φ.baseChange S) ∧
        Injective ((LinearMap.ker φ).subtype.baseChange S) := by
  obtain ⟨s, hs⟩ := exists_comp_comp_eq_of_isLocallyConstant_finrank_range φ h
  obtain ⟨r, hr⟩ := exists_retraction_range_of_generalizedInverse φ s hs
  obtain ⟨t, ht⟩ := exists_retraction_ker_of_generalizedInverse φ s hs
  have h1 : Module.Projective R (LinearMap.range φ) := Module.Projective.of_split _ r hr
  have h2 : Module.Finite R (LinearMap.ker φ) := Module.Finite.of_surjective t
    (RightInverse.surjective (g := (LinearMap.ker φ).subtype) (LinearMap.congr_fun ht))
  have h3 : Module.Projective R (LinearMap.ker φ) := Module.Projective.of_split _ t ht
  refine ⟨⟨inferInstance, h1⟩, ⟨h2, h3⟩,
    ⟨inferInstance, projective_coker_of_isLocallyConstant_finrank_range φ h⟩,
    ⟨_, LinearMap.isCompl_of_proj (LinearMap.congr_fun ht)⟩,
    ⟨_, LinearMap.isCompl_of_proj (LinearMap.congr_fun hr)⟩, fun p => ?_, fun p => ?_,
    fun S N _ _ _ _ _ _ => ⟨tensorKer_bijective_of_comp_comp_eq S N φ s hs,
      lTensor_subtype_injective_of_retraction _ r hr N⟩,
    fun S _ _ => ⟨baseChange_ker_of_comp_comp_eq φ s hs S,
      lTensor_subtype_injective_of_retraction _ t ht S⟩⟩
  · rw [Module.rankAtStalk_eq, ← baseChange_range]
    exact finrank_baseChange_eq_of_injective _ _ (lTensor_subtype_injective_of_retraction _ r hr _)
  · rw [Module.rankAtStalk_eq, ← baseChange_ker_of_comp_comp_eq φ s hs]
    exact finrank_baseChange_eq_of_injective _ _ (lTensor_subtype_injective_of_retraction _ t ht _)

end Map

universe u v w

theorem finite_projective_of_constant_fiber_rank {R : Type*} [CommRing R] [IsReduced R] :
    (∀ {E F : Type w} [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
      [Module.Finite R E] [Module.Projective R E] [Module.Finite R F] [Module.Projective R F]
      (φ : E →ₗ[R] F) (ρ : ℕ),
      (∀ p : PrimeSpectrum R, finrank p.asIdeal.ResidueField
        (LinearMap.range (φ.baseChange p.asIdeal.ResidueField)) = ρ) →
      (Module.Finite R (LinearMap.range φ) ∧ Module.Projective R (LinearMap.range φ)) ∧
      (Module.Finite R (LinearMap.ker φ) ∧ Module.Projective R (LinearMap.ker φ)) ∧
      (Module.Finite R (F ⧸ LinearMap.range φ) ∧ Module.Projective R (F ⧸ LinearMap.range φ)) ∧
      (∃ P : Submodule R E, IsCompl (LinearMap.ker φ) P) ∧
      (∃ Q : Submodule R F, IsCompl (LinearMap.range φ) Q) ∧
      (∀ p : PrimeSpectrum R, Module.rankAtStalk (LinearMap.range φ) p = ρ) ∧
      (∀ (S : Type u) (N : Type v) [CommRing S] [Algebra R S] [AddCommGroup N] [Module R N]
        [Module S N] [IsScalarTower R S N], Bijective (LinearMap.tensorKer S N φ)) ∧
      ∀ (S : Type u) [CommRing S] [Algebra R S],
        (LinearMap.ker φ).baseChange S = LinearMap.ker (φ.baseChange S) ∧
          Injective ((LinearMap.ker φ).subtype.baseChange S)) ∧
    ∀ {M : Type w} [AddCommGroup M] [Module R M] [Module.Finite R M] (ρ : ℕ),
      (∀ p : PrimeSpectrum R,
        finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M) = ρ) →
      Module.Projective R M ∧ ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = ρ := by
  refine ⟨fun φ ρ h => ?_, fun ρ h => projective_of_finite_of_finrank_fiber_eq ρ h⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, -, h7, h8⟩ :=
    finite_projective_of_isLocallyConstant_finrank_range.{u, v} φ
      (IsLocallyConstant.of_constant _ fun p q => (h p).trans (h q).symm)
  exact ⟨h1, h2, h3, h4, h5, fun p => (h6 p).trans (h p), fun S N _ _ _ _ _ _ => (h7 S N).1, h8⟩

example (p : PrimeSpectrum ℤ) : finrank p.asIdeal.ResidueField (LinearMap.range
    (((LinearMap.lsmul ℤ ℤ 2).coprod (LinearMap.lsmul ℤ ℤ 3)).baseChange
      p.asIdeal.ResidueField)) = 1 := by
  have hs : Surjective ((LinearMap.lsmul ℤ ℤ 2).coprod (LinearMap.lsmul ℤ ℤ 3)) :=
    fun z => ⟨(-z, z), by simp; ring⟩
  rw [← baseChange_range, LinearMap.range_eq_top.2 hs, Submodule.baseChange_top, finrank_top,
    Module.finrank_baseChange, Module.finrank_self]

end GlobalTheory
