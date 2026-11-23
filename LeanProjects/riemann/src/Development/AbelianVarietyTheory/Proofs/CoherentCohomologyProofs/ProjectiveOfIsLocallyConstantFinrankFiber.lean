import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapSpanBaseChangeEquivSubmoduleOf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisMapOfLiftBaseChangeSurjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso

open TensorProduct Module Function Filter Topology

namespace GlobalTheory

namespace Semicont

section Fibre

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

theorem baseChange_surjective_iff (S : Type*) [CommRing S] [Algebra R S] (φ : M →ₗ[R] N) :
    Surjective (φ.baseChange S) ↔ Subsingleton (S ⊗[R] (N ⧸ LinearMap.range φ)) := by
  rw [(baseChangeQuotEquiv S (LinearMap.range φ)).toEquiv.subsingleton_congr, baseChange_range,
    Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top]

theorem isOpen_setOf_baseChange_surjective [Module.Finite R N] (φ : M →ₗ[R] N) :
    IsOpen {p : PrimeSpectrum R | Surjective (φ.baseChange p.asIdeal.ResidueField)} := by
  have h := (Module.isClosed_support (R := R) (M := N ⧸ LinearMap.range φ)).isOpen_compl
  convert h using 1
  ext p
  rw [Set.mem_setOf_eq, baseChange_surjective_iff, Set.mem_compl_iff,
    Module.mem_support_iff_nontrivial_residueField_tensorProduct, not_nontrivial_iff_subsingleton]

theorem exists_baseChange_surjective [Module.Finite R M] (k : Type*) [Field k] [Algebra R k] :
    ∃ φ : (Fin (finrank k (k ⊗[R] M)) → R) →ₗ[R] M, Surjective (φ.baseChange k) := by
  obtain ⟨σ, b, -, hb⟩ := Avoid.exists_basis_map_one_tmul_of_surjective (K := R) (L := k) (V := M)
    rfl LinearMap.id surjective_id id (by simp)
  refine ⟨Fintype.linearCombination R σ, ?_⟩
  rw [← LinearMap.range_eq_top, eq_top_iff, ← b.span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact ⟨1 ⊗ₜ Pi.single j 1, by simp [hb]⟩

theorem finrank_baseChange_fin (k : Type*) [Field k] [Algebra R k] (n : ℕ) :
    finrank k (k ⊗[R] (Fin n → R)) = n := by
  rw [(TensorProduct.piScalarRight R k k (Fin n)).finrank_eq]
  simp

theorem eventually_finrank_fiber_le [Module.Finite R M] (p : PrimeSpectrum R) :
    ∀ᶠ q : PrimeSpectrum R in 𝓝 p,
      finrank q.asIdeal.ResidueField (q.asIdeal.ResidueField ⊗[R] M) ≤
        finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M) := by
  obtain ⟨φ, hφ⟩ := exists_baseChange_surjective (R := R) (M := M) p.asIdeal.ResidueField
  filter_upwards [(isOpen_setOf_baseChange_surjective φ).mem_nhds hφ] with q hq
  exact (LinearMap.finrank_le_finrank_of_surjective hq).trans_eq (finrank_baseChange_fin _ _)

variable (M) in

theorem upperSemicontinuous_finrank_fiber [Module.Finite R M] :
    UpperSemicontinuous fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M) := by
  intro p n hn
  filter_upwards [eventually_finrank_fiber_le (M := M) p] with q hq
  exact hq.trans_lt hn

variable (M) in

theorem isLocallyConstant_finrank_fiber [Module.Finite R M] [Module.Projective R M] :
    IsLocallyConstant fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M) := by
  have := Module.finitePresentation_of_projective R M
  convert Module.isLocallyConstant_rankAtStalk (R := R) (M := M) using 2 with p
  exact (Module.rankAtStalk_eq p).symm

theorem mem_freeLocus_of_eventually_finrank_eq [IsReduced R] [Module.Finite R M]
    (p : PrimeSpectrum R)
    (h : ∀ᶠ q : PrimeSpectrum R in 𝓝 p,
      finrank q.asIdeal.ResidueField (q.asIdeal.ResidueField ⊗[R] M) =
        finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M)) :
    p ∈ Module.freeLocus R M := by
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
    have h5 := congrFun (congrArg (TensorProduct.piScalarRight R J.ResidueField J.ResidueField _) h4) j
    refine J.mul_mem_left _ ?_
    rw [← Ideal.algebraMap_residueField_eq_zero]
    simpa [Algebra.smul_def] using h5
  let Rₚ := Localization.AtPrime p.asIdeal
  rw [Module.mem_freeLocus_iff_tensor p Rₚ]
  have hsurj : Surjective (φ.baseChange Rₚ) := by
    rw [baseChange_surjective_iff] at hφ ⊢
    rw [← not_nontrivial_iff_subsingleton,
      ← Module.mem_support_iff_nontrivial_residueField_tensorProduct,
      Module.notMem_support_iff] at hφ
    exact (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl _).symm.toEquiv.subsingleton
  have hinj : Injective (φ.baseChange Rₚ) := by
    rw [← LinearMap.ker_eq_bot, ← baseChange_ker, Submodule.baseChange_eq_span, eq_bot_iff,
      Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hu : IsUnit (algebraMap R Rₚ f) := IsLocalization.map_units Rₚ (⟨f, hpf⟩ : p.asIdeal.primeCompl)
    refine (hu.smul_eq_zero).1 ?_
    rw [algebraMap_smul, ← map_smul, hker x hx, map_zero]
  exact Module.Free.of_equiv (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩)

theorem projective_of_isLocallyConstant_finrank_fiber [IsReduced R] [Module.FinitePresentation R M]
    (h : IsLocallyConstant fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M)) :
    Module.Projective R M := by
  rw [← Module.freeLocus_eq_univ_iff, Set.eq_univ_iff_forall]
  exact fun p => mem_freeLocus_of_eventually_finrank_eq p (h.eventually_eq p)

end Fibre

section Regular

variable {R : Type*} [CommRing R] {M₀ M₁ M₂ : Type*} [AddCommGroup M₀] [Module R M₀]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

theorem exists_comp_comp_eq_of_projective (g : M₁ →ₗ[R] M₂) [Module.Projective R M₂]
    [Module.Projective R (M₂ ⧸ LinearMap.range g)] : ∃ s : M₂ →ₗ[R] M₁, g ∘ₗ s ∘ₗ g = g := by
  obtain ⟨t, ht⟩ := Module.projective_lifting_property (LinearMap.range g).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  have ht' : ∀ y, (LinearMap.range g).mkQ (t y) = y := fun y => LinearMap.congr_fun ht y
  let r : M₂ →ₗ[R] LinearMap.range g :=
    (LinearMap.id - t ∘ₗ (LinearMap.range g).mkQ).codRestrict _ fun x => by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, ht',
        sub_self]
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g.rangeRestrict r g.surjective_rangeRestrict
  refine ⟨s, LinearMap.ext fun x => ?_⟩
  have h0 : (LinearMap.range g).mkQ (g x) = 0 := by simp
  have := congrArg Subtype.val (LinearMap.congr_fun hs (g x))
  simpa [r, h0] using this

theorem exists_retraction_ker_of_projective (g : M₁ →ₗ[R] M₂)
    [Module.Projective R (LinearMap.range g)] :
    ∃ r : M₁ →ₗ[R] LinearMap.ker g, r ∘ₗ (LinearMap.ker g).subtype = LinearMap.id := by
  obtain ⟨t, ht⟩ := Module.projective_lifting_property g.rangeRestrict LinearMap.id
    g.surjective_rangeRestrict
  have ht' : ∀ y, g (t y) = y := fun y => congrArg Subtype.val (LinearMap.congr_fun ht y)
  refine ⟨(LinearMap.id - t ∘ₗ g.rangeRestrict).codRestrict _ fun x => by simp [ht'], ?_⟩
  ext x
  have : g.rangeRestrict x = 0 := Subtype.ext x.2
  simp [this]

theorem tensorKer_injective_of_retraction (S N : Type*) [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] (g : M₁ →ₗ[R] M₂)
    (r : M₁ →ₗ[R] LinearMap.ker g) (hr : r ∘ₗ (LinearMap.ker g).subtype = LinearMap.id) :
    Injective (LinearMap.tensorKer S N g) := by
  intro x y hxy
  have h := congrArg (fun z => r.lTensor N z.1) hxy
  simpa only [LinearMap.tensorKer_coe, ← LinearMap.lTensor_comp_apply, hr, LinearMap.lTensor_id,
    LinearMap.id_apply] using h

theorem tensorKer_bijective_of_comp_comp_eq (S N : Type*) [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] (g : M₁ →ₗ[R] M₂)
    (s : M₂ →ₗ[R] M₁) (hs : g ∘ₗ s ∘ₗ g = g) : Bijective (LinearMap.tensorKer S N g) := by
  have hs' : ∀ x, g (s (g x)) = g x := LinearMap.congr_fun hs
  let r : M₁ →ₗ[R] LinearMap.ker g :=
    (LinearMap.id - s ∘ₗ g).codRestrict _ fun x => by simp [hs']
  refine ⟨tensorKer_injective_of_retraction S N g r ?_, fun z => ⟨r.lTensor N z.1, ?_⟩⟩
  · ext x
    simp [r]
  · have hz : g.lTensor N z.1 = 0 := z.2
    ext
    rw [LinearMap.tensorKer_coe, ← LinearMap.lTensor_comp_apply, LinearMap.subtype_comp_codRestrict,
      LinearMap.lTensor_sub, LinearMap.lTensor_id, LinearMap.lTensor_comp, LinearMap.sub_apply,
      LinearMap.comp_apply, hz, map_zero, sub_zero, LinearMap.id_apply]

theorem exists_baseChange_homology_equiv (S : Type*) [CommRing S] [Algebra R S]
    (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂) (hfg : g ∘ₗ f = 0)
    (s : M₂ →ₗ[R] M₁) (hs : g ∘ₗ s ∘ₗ g = g) :
    ∃ e : S ⊗[R] (LinearMap.ker g ⧸ (LinearMap.range f).submoduleOf (LinearMap.ker g)) ≃ₗ[S]
        LinearMap.ker (g.baseChange S) ⧸
          (LinearMap.range (f.baseChange S)).submoduleOf (LinearMap.ker (g.baseChange S)),
      ∀ (a : S) (x : LinearMap.ker g), e (a ⊗ₜ Submodule.Quotient.mk x) =
        Submodule.Quotient.mk ⟨a ⊗ₜ (x : M₁), by simp⟩ := by
  let e₀ : S ⊗[R] LinearMap.ker g ≃ₗ[S] LinearMap.ker (g.baseChange S) :=
    LinearEquiv.ofBijective (LinearMap.tensorKer S S g)
      (tensorKer_bijective_of_comp_comp_eq S S g s hs)
  have he₀ : ∀ z, (e₀ z : S ⊗[R] M₁) = (LinearMap.ker g).subtype.baseChange S z :=
    fun z => LinearMap.tensorKer_coe S S g z
  let f' : M₀ →ₗ[R] LinearMap.ker g := f.codRestrict _ (LinearMap.congr_fun hfg)
  have hf' : (LinearMap.range f).submoduleOf (LinearMap.ker g) = LinearMap.range f' :=
    (LinearMap.range_codRestrict _ _ _).symm
  have hff' : ∀ y, (e₀ (f'.baseChange S y) : S ⊗[R] M₁) = f.baseChange S y := fun y => by
    rw [he₀, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    rfl
  refine ⟨baseChangeQuotEquiv S _ ≪≫ₗ Submodule.Quotient.equiv _ _ e₀ ?_, fun a x => rfl⟩
  rw [hf', baseChange_range]
  ext z
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, (hff' y).symm⟩
  · rintro ⟨y, hy⟩
    exact ⟨_, ⟨y, rfl⟩, Subtype.ext ((hff' y).trans hy)⟩

theorem exists_homology_retract (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂) (hfg : g ∘ₗ f = 0)
    (u : M₁ →ₗ[R] M₀) (hu : f ∘ₗ u ∘ₗ f = f) (s : M₂ →ₗ[R] M₁) (hs : g ∘ₗ s ∘ₗ g = g) :
    ∃ (ι : (LinearMap.ker g ⧸ (LinearMap.range f).submoduleOf (LinearMap.ker g)) →ₗ[R] M₁)
      (ρ : M₁ →ₗ[R] LinearMap.ker g ⧸ (LinearMap.range f).submoduleOf (LinearMap.ker g)),
      ρ ∘ₗ ι = LinearMap.id := by
  have hs' : ∀ x, g (s (g x)) = g x := LinearMap.congr_fun hs
  have hu' : ∀ x, f (u (f x)) = f x := LinearMap.congr_fun hu
  have hfg' : ∀ x, g (f x) = 0 := LinearMap.congr_fun hfg
  refine ⟨Submodule.liftQ _ ((LinearMap.id - f ∘ₗ u) ∘ₗ (LinearMap.ker g).subtype) ?_,
    Submodule.mkQ _ ∘ₗ (LinearMap.id - s ∘ₗ g).codRestrict _ fun x => by simp [hs'], ?_⟩
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain rfl : f y = x := hy
    simp [hu']
  · refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
    refine (Submodule.Quotient.eq _).2 ⟨-u x, ?_⟩
    simp [hfg']

end Regular

section Field

variable {k : Type*} [Field k] {V₀ V₁ V₂ : Type*} [AddCommGroup V₀] [Module k V₀]
  [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]

theorem finrank_homology_add_finrank_range [Module.Finite k V₁]
    (f : V₀ →ₗ[k] V₁) (g : V₁ →ₗ[k] V₂) (hfg : g ∘ₗ f = 0) :
    finrank k (LinearMap.ker g ⧸ (LinearMap.range f).submoduleOf (LinearMap.ker g)) +
      finrank k (LinearMap.range f) + finrank k (LinearMap.range g) = finrank k V₁ := by
  have h1 := Submodule.finrank_quotient_add_finrank
    ((LinearMap.range f).submoduleOf (LinearMap.ker g))
  rw [(Submodule.submoduleOfEquivOfLe (LinearMap.range_le_ker_iff.2 hfg)).finrank_eq] at h1
  have h2 := g.finrank_range_add_finrank_ker
  omega

theorem finrank_homology_add_finrank [Module.Finite k V₁] [Module.Finite k V₂]
    (f : V₀ →ₗ[k] V₁) (g : V₁ →ₗ[k] V₂) (hfg : g ∘ₗ f = 0) :
    finrank k (LinearMap.ker g ⧸ (LinearMap.range f).submoduleOf (LinearMap.ker g)) +
      finrank k V₂ = finrank k (V₁ ⧸ LinearMap.range f) + finrank k (V₂ ⧸ LinearMap.range g) := by
  have h1 := finrank_homology_add_finrank_range f g hfg
  have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.range f)
  have h3 := Submodule.finrank_quotient_add_finrank (LinearMap.range g)
  omega

end Field

section ThreeTerm

variable {R : Type*} [CommRing R] {M₀ M₁ M₂ : Type*} [AddCommGroup M₀] [Module R M₀]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

theorem finrank_baseChange_homology_add (k : Type*) [Field k] [Algebra R k]
    [Module.Finite R M₁] [Module.Finite R M₂]
    (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂) (hfg : g ∘ₗ f = 0) :
    finrank k (LinearMap.ker (g.baseChange k) ⧸
        (LinearMap.range (f.baseChange k)).submoduleOf (LinearMap.ker (g.baseChange k))) +
      finrank k (k ⊗[R] M₂) =
      finrank k (k ⊗[R] (M₁ ⧸ LinearMap.range f)) + finrank k (k ⊗[R] (M₂ ⧸ LinearMap.range g)) := by
  rw [(baseChangeQuotEquiv k _).finrank_eq, (baseChangeQuotEquiv k _).finrank_eq,
    baseChange_range, baseChange_range]
  exact finrank_homology_add_finrank _ _
    (by rw [← LinearMap.baseChange_comp, hfg, LinearMap.baseChange_zero])

theorem upperSemicontinuous_finrank_linearMap_homology
    [Module.Finite R M₁] [Module.Finite R M₂] [Module.Projective R M₂]
    (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂) (hfg : g ∘ₗ f = 0) :
    UpperSemicontinuous fun p : PrimeSpectrum R => finrank p.asIdeal.ResidueField
      (LinearMap.ker (g.baseChange p.asIdeal.ResidueField) ⧸
        (LinearMap.range (f.baseChange p.asIdeal.ResidueField)).submoduleOf
          (LinearMap.ker (g.baseChange p.asIdeal.ResidueField))) := by
  intro p n hn
  filter_upwards [eventually_finrank_fiber_le (M := M₁ ⧸ LinearMap.range f) p,
    eventually_finrank_fiber_le (M := M₂ ⧸ LinearMap.range g) p,
    (isLocallyConstant_finrank_fiber M₂).eventually_eq p] with q h1 h2 h3
  have h4 := finrank_baseChange_homology_add p.asIdeal.ResidueField f g hfg
  have h5 := finrank_baseChange_homology_add q.asIdeal.ResidueField f g hfg
  beta_reduce at hn ⊢
  omega

theorem projective_coker_of_isLocallyConstant [IsReduced R] [Module.Finite R M₀]
    [Module.Finite R M₁] [Module.Projective R M₁] [Module.Finite R M₂] [Module.Projective R M₂]
    (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂) (hfg : g ∘ₗ f = 0)
    (h : IsLocallyConstant fun p : PrimeSpectrum R => finrank p.asIdeal.ResidueField
      (LinearMap.ker (g.baseChange p.asIdeal.ResidueField) ⧸
        (LinearMap.range (f.baseChange p.asIdeal.ResidueField)).submoduleOf
          (LinearMap.ker (g.baseChange p.asIdeal.ResidueField)))) :
    Module.Projective R (M₁ ⧸ LinearMap.range f) ∧ Module.Projective R (M₂ ⧸ LinearMap.range g) := by
  have := Module.finitePresentation_of_projective R M₁
  have := Module.finitePresentation_of_projective R M₂
  have : Module.FinitePresentation R (M₁ ⧸ LinearMap.range f) :=
    Module.finitePresentation_of_surjective _ (Submodule.mkQ_surjective _)
      (by rw [Submodule.ker_mkQ]; exact Submodule.fg_range f)
  have : Module.FinitePresentation R (M₂ ⧸ LinearMap.range g) :=
    Module.finitePresentation_of_surjective _ (Submodule.mkQ_surjective _)
      (by rw [Submodule.ker_mkQ]; exact Submodule.fg_range g)
  constructor
  all_goals
    refine projective_of_isLocallyConstant_finrank_fiber
      ((IsLocallyConstant.iff_eventually_eq _).2 fun p => ?_)
    filter_upwards [eventually_finrank_fiber_le (M := M₁ ⧸ LinearMap.range f) p,
      eventually_finrank_fiber_le (M := M₂ ⧸ LinearMap.range g) p,
      (isLocallyConstant_finrank_fiber M₂).eventually_eq p, h.eventually_eq p] with q h1 h2 h3 h6
    have h4 := finrank_baseChange_homology_add p.asIdeal.ResidueField f g hfg
    have h5 := finrank_baseChange_homology_add q.asIdeal.ResidueField f g hfg
    omega

theorem grauert_linearMap_homology [IsReduced R] [Module.Finite R M₀]
    [Module.Finite R M₁] [Module.Projective R M₁] [Module.Finite R M₂] [Module.Projective R M₂]
    (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂) (hfg : g ∘ₗ f = 0)
    (h : IsLocallyConstant fun p : PrimeSpectrum R => finrank p.asIdeal.ResidueField
      (LinearMap.ker (g.baseChange p.asIdeal.ResidueField) ⧸
        (LinearMap.range (f.baseChange p.asIdeal.ResidueField)).submoduleOf
          (LinearMap.ker (g.baseChange p.asIdeal.ResidueField)))) :
    Module.Finite R (LinearMap.ker g ⧸ (LinearMap.range f).submoduleOf (LinearMap.ker g)) ∧
    Module.Projective R (LinearMap.ker g ⧸ (LinearMap.range f).submoduleOf (LinearMap.ker g)) ∧
    ∀ (S : Type*) [CommRing S] [Algebra R S],
      ∃ e : S ⊗[R] (LinearMap.ker g ⧸ (LinearMap.range f).submoduleOf (LinearMap.ker g)) ≃ₗ[S]
          LinearMap.ker (g.baseChange S) ⧸
            (LinearMap.range (f.baseChange S)).submoduleOf (LinearMap.ker (g.baseChange S)),
        ∀ (a : S) (x : LinearMap.ker g), e (a ⊗ₜ Submodule.Quotient.mk x) =
          Submodule.Quotient.mk ⟨a ⊗ₜ (x : M₁), by simp⟩ := by
  obtain ⟨h1, h2⟩ := projective_coker_of_isLocallyConstant f g hfg h
  obtain ⟨u, hu⟩ := exists_comp_comp_eq_of_projective f
  obtain ⟨s, hs⟩ := exists_comp_comp_eq_of_projective g
  obtain ⟨ι, ρ, hρ⟩ := exists_homology_retract f g hfg u hu s hs
  exact ⟨Module.Finite.of_surjective ρ
      (RightInverse.surjective (g := ι) (LinearMap.congr_fun hρ)),
    Module.Projective.of_split ι ρ hρ,
    fun S _ _ => exists_baseChange_homology_equiv S f g hfg s hs⟩

end ThreeTerm

section Valuation

variable {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R] {M₀ M₁ : Type*}
  [AddCommGroup M₀] [Module R M₀] [AddCommGroup M₁] [Module R M₁]

variable (R) in

theorem free_of_finite_of_isTorsionFree (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.IsTorsionFree R M] : Module.Free R M := by
  have : Module.Flat R M := Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2
    (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)
  exact Module.free_of_flat_of_isLocalRing

theorem ker_of_valuationRing [Module.Finite R M₀] [Module.IsTorsionFree R M₀]
    [Module.IsTorsionFree R M₁] (d : M₀ →ₗ[R] M₁) :
    Module.Free R (LinearMap.range d) ∧
    Module.Finite R (LinearMap.ker d) ∧ Module.Free R (LinearMap.ker d) ∧
    (∃ N : Submodule R M₀, IsCompl (LinearMap.ker d) N) ∧
    ∀ (S N : Type*) [CommRing S] [Algebra R S] [AddCommGroup N] [Module R N] [Module S N]
      [IsScalarTower R S N], Injective (LinearMap.tensorKer S N d) ∧
        (Module.Flat R N → Bijective (LinearMap.tensorKer S N d)) := by
  have h1 := free_of_finite_of_isTorsionFree R (LinearMap.range d)
  obtain ⟨r, hr⟩ := exists_retraction_ker_of_projective d
  have h2 : Module.Finite R (LinearMap.ker d) := Module.Finite.of_surjective r
    (RightInverse.surjective (g := (LinearMap.ker d).subtype) (LinearMap.congr_fun hr))
  exact ⟨h1, h2, free_of_finite_of_isTorsionFree R _,
    ⟨_, LinearMap.isCompl_of_proj (LinearMap.congr_fun hr)⟩,
    fun S N _ _ _ _ _ _ => ⟨tensorKer_injective_of_retraction S N d r hr,
      fun _ => (LinearMap.tensorKerEquiv S N d).bijective⟩⟩

end Valuation

section Additive

open CategoryTheory Limits

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  (F : C ⥤ D) [F.Additive]

theorem preservesKernel_of_comp_comp_eq {X Y : C} (g : X ⟶ Y) [HasKernel g] (s : Y ⟶ X)
    (hs : g ≫ s ≫ g = g) : PreservesLimit (parallelPair g 0) F := by
  let r : X ⟶ kernel g := kernel.lift g (𝟙 X - g ≫ s) (by simp [Preadditive.sub_comp, hs])
  have h1 : r ≫ kernel.ι g = 𝟙 X - g ≫ s := kernel.lift_ι _ _ _
  have h2 : kernel.ι g ≫ r = 𝟙 _ := by
    rw [← cancel_mono (kernel.ι g)]
    simp [h1, Preadditive.comp_sub]
  have : Mono (F.map (kernel.ι g)) :=
    (SplitMono.mk (f := F.map (kernel.ι g)) (F.map r) (by rw [← F.map_comp, h2, F.map_id])).mono
  refine preservesLimit_of_preserves_limit_cone (kernelIsKernel g)
    ((isLimitMapConeForkEquiv' F (kernel.condition g)).symm (KernelFork.IsLimit.ofι' _
      (by rw [← F.map_comp, kernel.condition, F.map_zero]) fun k hk => ⟨k ≫ F.map r, ?_⟩))
  rw [Category.assoc, ← F.map_comp, h1, F.map_sub, F.map_id, F.map_comp, Preadditive.comp_sub,
    reassoc_of% hk, zero_comp, sub_zero, Category.comp_id]

theorem preservesCokernel_of_comp_comp_eq {X Y : C} (f : X ⟶ Y) [HasCokernel f] (u : Y ⟶ X)
    (hu : f ≫ u ≫ f = f) : PreservesColimit (parallelPair f 0) F := by
  let t : cokernel f ⟶ Y := cokernel.desc f (𝟙 Y - u ≫ f) (by simp [Preadditive.comp_sub, hu])
  have h1 : cokernel.π f ≫ t = 𝟙 Y - u ≫ f := cokernel.π_desc _ _ _
  have h2 : t ≫ cokernel.π f = 𝟙 _ := by
    rw [← cancel_epi (cokernel.π f)]
    simp [reassoc_of% h1, Preadditive.sub_comp]
  have : Epi (F.map (cokernel.π f)) :=
    (SplitEpi.mk (f := F.map (cokernel.π f)) (F.map t) (by rw [← F.map_comp, h2, F.map_id])).epi
  refine preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
    ((isColimitMapCoconeCoforkEquiv' F (cokernel.condition f)).symm
      (CokernelCofork.IsColimit.ofπ' _ (by rw [← F.map_comp, cokernel.condition, F.map_zero])
        fun k hk => ⟨F.map t ≫ k, ?_⟩))
  rw [← F.map_comp_assoc, h1, F.map_sub, F.map_id, F.map_comp, Preadditive.sub_comp,
    Category.assoc, hk, comp_zero, sub_zero, Category.id_comp]

theorem preservesLeftHomologyOf_of_comp_comp_eq (S : ShortComplex C) (u : S.X₂ ⟶ S.X₁)
    (hu : S.f ≫ u ≫ S.f = S.f) (s : S.X₃ ⟶ S.X₂) (hs : S.g ≫ s ≫ S.g = S.g) :
    F.PreservesLeftHomologyOf S := by
  refine ⟨fun h => ?_⟩
  have : HasKernel S.g := ⟨⟨_, h.hi⟩⟩
  have : HasCokernel h.f' := ⟨⟨_, h.hπ'⟩⟩
  exact ⟨preservesKernel_of_comp_comp_eq F _ s hs,
    preservesCokernel_of_comp_comp_eq F _ (h.i ≫ u) (by simp [← cancel_mono h.i, hu])⟩

theorem preservesRightHomologyOf_of_comp_comp_eq (S : ShortComplex C) (u : S.X₂ ⟶ S.X₁)
    (hu : S.f ≫ u ≫ S.f = S.f) (s : S.X₃ ⟶ S.X₂) (hs : S.g ≫ s ≫ S.g = S.g) :
    F.PreservesRightHomologyOf S := by
  refine ⟨fun h => ?_⟩
  have : HasCokernel S.f := ⟨⟨_, h.hp⟩⟩
  have : HasKernel h.g' := ⟨⟨_, h.hι'⟩⟩
  exact ⟨preservesCokernel_of_comp_comp_eq F _ u hu,
    preservesKernel_of_comp_comp_eq F _ (s ≫ h.p) (by simp [← cancel_epi h.p, hs])⟩

end Additive

section Complex

open CategoryTheory Limits

universe v u₁ u₂

theorem nonempty_homology_equiv {R : Type u₁} [Ring R] (S : ShortComplex (ModuleCat.{v} R)) :
    Nonempty (S.homology ≃ₗ[R] (LinearMap.ker S.g.hom ⧸
      (LinearMap.range S.f.hom).submoduleOf (LinearMap.ker S.g.hom))) :=
  ⟨S.moduleCatHomologyIso.toLinearEquiv ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (LinearMap.range_codRestrict _ _ _)⟩

theorem nonempty_homology_map_extendScalars_equiv {R : Type u₁} (A : Type u₂) [CommRing R]
    [CommRing A] [inst : Algebra R A] (S : ShortComplex (ModuleCat.{v} R)) :
    Nonempty ((S.map (ModuleCat.extendScalars (algebraMap R A))).homology ≃ₗ[A]
      (LinearMap.ker (S.g.hom.baseChange A) ⧸
        (LinearMap.range (S.f.hom.baseChange A)).submoduleOf
          (LinearMap.ker (S.g.hom.baseChange A)))) := by
  obtain ⟨φ, rfl⟩ : ∃ φ : R →+* A, inst = φ.toAlgebra :=
    ⟨algebraMap R A, Algebra.algebra_ext _ _ fun _ => rfl⟩
  exact nonempty_homology_equiv (S.map (ModuleCat.extendScalars φ))

theorem nonempty_extendScalars_obj_equiv {R : Type u₁} (A : Type u₂) [CommRing R]
    [CommRing A] [inst : Algebra R A] (M : ModuleCat.{v} R) :
    Nonempty ((ModuleCat.extendScalars (algebraMap R A)).obj M ≃ₗ[A] A ⊗[R] M) := by
  obtain ⟨φ, rfl⟩ : ∃ φ : R →+* A, inst = φ.toAlgebra :=
    ⟨algebraMap R A, Algebra.algebra_ext _ _ fun _ => rfl⟩
  exact ⟨LinearEquiv.refl _ _⟩

theorem sum_finrank_homology_eq {k : Type u₁} [Field k] {ι : Type*} {c : ComplexShape ι}
    [c.EulerCharSigns] (K : HomologicalComplex (ModuleCat.{v} k) c)
    [∀ i, Module.Finite k (K.X i)] (s : Finset ι) (hs : ∀ i ∉ s, IsZero (K.X i)) :
    ∑ i ∈ s, (c.χ i : ℤ) * finrank k (K.homology i) = ∑ i ∈ s, (c.χ i : ℤ) * finrank k (K.X i) := by
  let r : ι → ι → ℕ := fun i j => finrank k (LinearMap.range (K.d i j).hom)
  have hr : ∀ i j, r i j ≠ 0 → c.Rel i j ∧ i ∈ s ∧ j ∈ s := by
    intro i j h
    have hd : K.d i j ≠ 0 := fun h0 => h (by simp [r, h0])
    refine ⟨?_, ?_, ?_⟩ <;> by_contra h'
    exacts [hd (K.shape i j h'), hd ((hs i h').eq_of_src _ _), hd ((hs j h').eq_of_tgt _ _)]
  have hx : ∀ i, finrank k (K.homology i) + r (c.prev i) i + r i (c.next i) = finrank k (K.X i) := by
    intro i
    obtain ⟨e⟩ := nonempty_homology_equiv (K.sc i)
    have : Module.Finite k (K.sc i).X₂ := inferInstanceAs (Module.Finite k (K.X i))
    have h := finrank_homology_add_finrank_range (K.sc i).f.hom (K.sc i).g.hom
      (congrArg ModuleCat.Hom.hom (K.sc i).zero)
    rw [← e.finrank_eq] at h
    exact h
  have hsum : ∑ i ∈ s, (c.χ i : ℤ) * r i (c.next i) =
      ∑ j ∈ s, -((c.χ j : ℤ) * r (c.prev j) j) := by
    have h1 : ∀ i, (c.χ i : ℤ) * r i (c.next i) ≠ 0 → r i (c.next i) ≠ 0 := fun i h h0 =>
      h (by simp [h0])
    refine Finset.sum_bij_ne_zero (fun i _ _ => c.next i) (fun i _ h => (hr _ _ (h1 i h)).2.2)
      (fun i _ h i' _ h' e => c.prev_eq (hr _ _ (h1 i h)).1 (e ▸ (hr _ _ (h1 i' h')).1))
      (fun j _ h => ?_) (fun i _ h => ?_)
    · have h2 : r (c.prev j) j ≠ 0 := fun h0 => h (by simp [h0])
      have h3 := c.next_eq' (hr _ _ h2).1
      exact ⟨c.prev j, (hr _ _ h2).2.1, by simpa [h3] using h2, h3⟩
    · have h2 := (hr _ _ (h1 i h)).1
      rw [c.prev_eq' h2, c.χ_next h2]
      simp
  simp only [← hx, Nat.cast_add, mul_add, Finset.sum_add_distrib, hsum, Finset.sum_neg_distrib]
  ring

end Complex

end Semicont

section Main

open CategoryTheory Limits Semicont

universe v u w

variable {R : Type u} [CommRing R] {ι : Type*} {c : ComplexShape ι}

theorem finite_homology_extendScalars (K : HomologicalComplex (ModuleCat.{v} R) c) (i : ι)
    [Module.Finite R (K.X i)] (A : Type w) [CommRing A] [IsNoetherianRing A] [Algebra R A] :
    Module.Finite A
      ((((ModuleCat.extendScalars (algebraMap R A)).mapHomologicalComplex c).obj K).homology i) := by
  obtain ⟨e⟩ := nonempty_homology_map_extendScalars_equiv A (K.sc i)
  have : Module.Finite R (K.sc i).X₂ := inferInstanceAs (Module.Finite R (K.X i))
  exact Module.Finite.equiv e.symm

theorem upperSemicontinuous_finrank_homology_fiber (K : HomologicalComplex (ModuleCat.{v} R) c)
    [∀ i, Module.Finite R (K.X i)] [∀ i, Module.Projective R (K.X i)] (i : ι) :
    UpperSemicontinuous fun p : PrimeSpectrum R => finrank p.asIdeal.ResidueField
      ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
        c).obj K).homology i) := by
  have : Module.Finite R (K.sc i).X₂ := inferInstanceAs (Module.Finite R (K.X i))
  have : Module.Finite R (K.sc i).X₃ := inferInstanceAs (Module.Finite R (K.X _))
  have : Module.Projective R (K.sc i).X₃ := inferInstanceAs (Module.Projective R (K.X _))
  convert upperSemicontinuous_finrank_linearMap_homology (K.sc i).f.hom (K.sc i).g.hom
    (congrArg ModuleCat.Hom.hom (K.sc i).zero) using 2 with p
  exact (nonempty_homology_map_extendScalars_equiv _ (K.sc i)).elim fun e => e.finrank_eq

theorem sum_finrank_homology_extendScalars [c.EulerCharSigns]
    (K : HomologicalComplex (ModuleCat.{v} R) c) [∀ i, Module.Finite R (K.X i)]
    (s : Finset ι) (hs : ∀ i ∉ s, IsZero (K.X i)) (k : Type w) [Field k] [Algebra R k] :
    ∑ i ∈ s, (c.χ i : ℤ) * finrank k
      ((((ModuleCat.extendScalars (algebraMap R k)).mapHomologicalComplex c).obj K).homology i) =
    ∑ i ∈ s, (c.χ i : ℤ) * finrank k (k ⊗[R] K.X i) := by
  have : ∀ i, Module.Finite k
      ((((ModuleCat.extendScalars (algebraMap R k)).mapHomologicalComplex c).obj K).X i) :=
    fun i => (nonempty_extendScalars_obj_equiv k (K.X i)).elim fun e => Module.Finite.equiv e.symm
  rw [sum_finrank_homology_eq _ s
    fun i hi => (ModuleCat.extendScalars (algebraMap R k)).map_isZero (hs i hi)]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  exact (nonempty_extendScalars_obj_equiv k (K.X i)).elim fun e => e.finrank_eq

theorem sum_finrank_homology_fiber_eq_sum_rankAtStalk [c.EulerCharSigns]
    (K : HomologicalComplex (ModuleCat.{v} R) c)
    [∀ i, Module.Finite R (K.X i)] [∀ i, Module.Projective R (K.X i)]
    (s : Finset ι) (hs : ∀ i ∉ s, IsZero (K.X i)) (p : PrimeSpectrum R) :
    ∑ i ∈ s, (c.χ i : ℤ) * finrank p.asIdeal.ResidueField
      ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
        c).obj K).homology i) = ∑ i ∈ s, (c.χ i : ℤ) * Module.rankAtStalk (R := R) (K.X i) p := by
  rw [sum_finrank_homology_extendScalars K s hs]
  exact Finset.sum_congr rfl fun i _ => by rw [Module.rankAtStalk_eq]

theorem isLocallyConstant_sum_finrank_homology_fiber [c.EulerCharSigns]
    (K : HomologicalComplex (ModuleCat.{v} R) c)
    [∀ i, Module.Finite R (K.X i)] [∀ i, Module.Projective R (K.X i)]
    (s : Finset ι) (hs : ∀ i ∉ s, IsZero (K.X i)) :
    IsLocallyConstant fun p : PrimeSpectrum R => ∑ i ∈ s, (c.χ i : ℤ) *
      finrank p.asIdeal.ResidueField
        ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
          c).obj K).homology i) := by
  simp only [sum_finrank_homology_extendScalars K s hs]
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun p => ?_
  filter_upwards [(Filter.eventually_all_finset s).2 fun i _ =>
    (isLocallyConstant_finrank_fiber (R := R) (K.X i)).eventually_eq p] with q hq
  exact Finset.sum_congr rfl fun i hi => by rw [hq i hi]

theorem isLocallyConstant_homologyEulerChar_fiber [c.EulerCharSigns]
    (K : HomologicalComplex (ModuleCat.{v} R) c)
    [∀ i, Module.Finite R (K.X i)] [∀ i, Module.Projective R (K.X i)]
    (s : Finset ι) (hs : ∀ i ∉ s, IsZero (K.X i)) :
    IsLocallyConstant fun p : PrimeSpectrum R =>
      (((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
        c).obj K).homologyEulerChar := by
  convert isLocallyConstant_sum_finrank_homology_fiber K s hs using 2 with p
  refine HomologicalComplex.homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset _ s
    ((GradedObject.finrankSupport_subset_iff _ _).2 fun i hi => ?_)
  have := ModuleCat.isZero_iff_subsingleton.1
    (ShortComplex.isZero_homology_of_isZero_X₂
      ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
        c).obj K).sc i) ((ModuleCat.extendScalars _).map_isZero (hs i hi)))
  exact @Module.finrank_zero_of_subsingleton _ _ _ _ _ _ this

theorem isLocallyConstant_sum_range_finrank_homology_fiber
    (K : CochainComplex (ModuleCat.{v} R) ℕ)
    [∀ i, Module.Finite R (K.X i)] [∀ i, Module.Projective R (K.X i)]
    (n : ℕ) (hn : ∀ i, n < i → IsZero (K.X i)) :
    IsLocallyConstant fun p : PrimeSpectrum R => ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
      finrank p.asIdeal.ResidueField
        ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
          _).obj K).homology i) := by
  convert isLocallyConstant_sum_finrank_homology_fiber K (Finset.range (n + 1))
    (fun i hi => hn i (by simpa using hi)) using 4 with p i
  simp [ComplexShape.χ]

theorem map_iCycles_d {C D : Type*} [Category* C] [Category* D] [Abelian C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (K : HomologicalComplex C c) (i j : ι) :
    F.map (K.iCycles i) ≫ ((F.mapHomologicalComplex c).obj K).d i j = 0 :=
  (F.map_comp _ _).symm.trans ((congrArg F.map (K.iCycles_d i j)).trans (F.map_zero _ _))

theorem exists_map_homology_iso {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] (K : HomologicalComplex C c) (i : ι)
    [F.PreservesLeftHomologyOf (K.sc i)] :
    ∃ e : F.obj (K.homology i) ≅ ((F.mapHomologicalComplex c).obj K).homology i,
      F.map (K.homologyπ i) ≫ e.hom =
        ((F.mapHomologicalComplex c).obj K).liftCycles (F.map (K.iCycles i)) (c.next i) rfl
          (map_iCycles_d F K i _) ≫ ((F.mapHomologicalComplex c).obj K).homologyπ i := by
  let h := (ShortComplex.LeftHomologyData.canonical (K.sc i)).map F
  refine ⟨h.homologyIso.symm, h.π_comp_homologyIso_inv.trans ?_⟩
  refine congrArg (· ≫ ((K.sc i).map F).homologyπ) ?_
  exact (cancel_mono ((K.sc i).map F).iCycles).1 (h.cyclesIso_inv_comp_iCycles.trans
    (((F.mapHomologicalComplex c).obj K).liftCycles_i _ _ _ _).symm)

theorem exists_generalizedInverse_of_isLocallyConstant [IsReduced R]
    (K : HomologicalComplex (ModuleCat.{v} R) c)
    [∀ i, Module.Finite R (K.X i)] [∀ i, Module.Projective R (K.X i)] (i : ι)
    (h : IsLocallyConstant fun p : PrimeSpectrum R => finrank p.asIdeal.ResidueField
      ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
        c).obj K).homology i)) :
    (∃ u : K.X i ⟶ K.X (c.prev i),
      K.d (c.prev i) i ≫ u ≫ K.d (c.prev i) i = K.d (c.prev i) i) ∧
    ∃ s : K.X (c.next i) ⟶ K.X i, K.d i (c.next i) ≫ s ≫ K.d i (c.next i) = K.d i (c.next i) := by
  obtain ⟨h1, h2⟩ := projective_coker_of_isLocallyConstant (K.d (c.prev i) i).hom
    (K.d i (c.next i)).hom (congrArg ModuleCat.Hom.hom (K.sc i).zero) (by
      convert h using 2 with p
      exact (nonempty_homology_map_extendScalars_equiv _ (K.sc i)).elim fun e => e.finrank_eq.symm)
  obtain ⟨u, hu⟩ := exists_comp_comp_eq_of_projective (K.d (c.prev i) i).hom
  obtain ⟨s, hs⟩ := exists_comp_comp_eq_of_projective (K.d i (c.next i)).hom
  exact ⟨⟨ModuleCat.ofHom u, ModuleCat.hom_ext hu⟩, ModuleCat.ofHom s, ModuleCat.hom_ext hs⟩

theorem preservesHomologyOf_of_isLocallyConstant [IsReduced R]
    (K : HomologicalComplex (ModuleCat.{v} R) c)
    [∀ i, Module.Finite R (K.X i)] [∀ i, Module.Projective R (K.X i)] (i : ι)
    (h : IsLocallyConstant fun p : PrimeSpectrum R => finrank p.asIdeal.ResidueField
      ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
        c).obj K).homology i))
    {D : Type*} [Category* D] [Preadditive D] (F : ModuleCat.{v} R ⥤ D) [F.Additive] :
    F.PreservesLeftHomologyOf (K.sc i) ∧ F.PreservesRightHomologyOf (K.sc i) := by
  obtain ⟨⟨u, hu⟩, s, hs⟩ := exists_generalizedInverse_of_isLocallyConstant K i h
  exact ⟨preservesLeftHomologyOf_of_comp_comp_eq F (K.sc i) u hu s hs,
    preservesRightHomologyOf_of_comp_comp_eq F (K.sc i) u hu s hs⟩

theorem grauert_homology [IsReduced R] (K : HomologicalComplex (ModuleCat.{v} R) c)
    [∀ i, Module.Finite R (K.X i)] [∀ i, Module.Projective R (K.X i)] (i : ι)
    (h : IsLocallyConstant fun p : PrimeSpectrum R => finrank p.asIdeal.ResidueField
      ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
        c).obj K).homology i)) :
    Module.Finite R (K.homology i) ∧ Module.Projective R (K.homology i) ∧
    ∀ (S : Type w) [CommRing S] (φ : R →+* S),
      ∃ e : (ModuleCat.extendScalars φ).obj (K.homology i) ≅
          (((ModuleCat.extendScalars φ).mapHomologicalComplex c).obj K).homology i,
        (ModuleCat.extendScalars φ).map (K.homologyπ i) ≫ e.hom =
          (((ModuleCat.extendScalars φ).mapHomologicalComplex c).obj K).liftCycles
            ((ModuleCat.extendScalars φ).map (K.iCycles i)) (c.next i) rfl
            (map_iCycles_d _ K i _) ≫
          (((ModuleCat.extendScalars φ).mapHomologicalComplex c).obj K).homologyπ i := by
  obtain ⟨⟨u, hu⟩, s, hs⟩ := exists_generalizedInverse_of_isLocallyConstant K i h
  obtain ⟨j, ρ, hρ⟩ := exists_homology_retract (K.d (c.prev i) i).hom (K.d i (c.next i)).hom
    (congrArg ModuleCat.Hom.hom (K.sc i).zero) u.hom (congrArg ModuleCat.Hom.hom hu)
    s.hom (congrArg ModuleCat.Hom.hom hs)
  obtain ⟨e⟩ := nonempty_homology_equiv (K.sc i)
  have h1 := Module.Finite.of_surjective ρ (RightInverse.surjective (g := j) (LinearMap.congr_fun hρ))
  have h2 := Module.Projective.of_split j ρ hρ
  refine ⟨@Module.Finite.equiv _ _ _ _ _ _ _ _ h1 e.symm,
    @Module.Projective.of_equiv' _ _ _ _ _ _ _ _ h2 e.symm, fun S _ φ => ?_⟩
  have := (preservesHomologyOf_of_isLocallyConstant K i h (ModuleCat.extendScalars φ)).1
  exact exists_map_homology_iso _ K i

theorem ker_free_of_valuationRing {O : Type*} [CommRing O] [IsDomain O] [ValuationRing O]
    (F : Type*) [Field F] [Algebra O F] [IsFractionRing O F]
    {M₀ M₁ : Type*} [AddCommGroup M₀] [Module O M₀] [AddCommGroup M₁] [Module O M₁]
    [Module.Finite O M₀] [Module.Projective O M₀] [Module.Projective O M₁] (d : M₀ →ₗ[O] M₁) :
    Module.Finite O (LinearMap.ker d) ∧ Module.Free O (LinearMap.ker d) ∧
    (∃ N : Submodule O M₀, IsCompl (LinearMap.ker d) N) ∧
    Bijective (LinearMap.tensorKer F F d) ∧
    Injective (LinearMap.tensorKer (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O) d) := by
  obtain ⟨-, h1, h2, h3, -⟩ := ker_of_valuationRing.{_, _, _, 0, 0} d
  have := IsLocalization.flat F (nonZeroDivisors O)
  exact ⟨h1, h2, h3, (LinearMap.tensorKerEquiv F F d).bijective,
    ((ker_of_valuationRing d).2.2.2.2 _ _).1⟩

theorem semicontinuity_finite_projective_complex (K : CochainComplex (ModuleCat.{v} R) ℕ)
    [∀ i, Module.Finite R (K.X i)] [∀ i, Module.Projective R (K.X i)]
    (n : ℕ) (hn : ∀ i, n < i → IsZero (K.X i)) :
    (∀ (i : ℕ) (p : PrimeSpectrum R), Module.Finite p.asIdeal.ResidueField
      ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
        _).obj K).homology i)) ∧
    (∀ i : ℕ, UpperSemicontinuous fun p : PrimeSpectrum R => finrank p.asIdeal.ResidueField
      ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
        _).obj K).homology i)) ∧
    (IsLocallyConstant fun p : PrimeSpectrum R => ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
      finrank p.asIdeal.ResidueField
        ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
          _).obj K).homology i)) ∧
    (∀ i : ℕ, IsReduced R →
      (IsLocallyConstant fun p : PrimeSpectrum R => finrank p.asIdeal.ResidueField
        ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
          _).obj K).homology i)) →
      Module.Finite R (K.homology i) ∧ Module.Projective R (K.homology i) ∧
      ∀ (S : Type u) [CommRing S] (φ : R →+* S),
        ∃ e : (ModuleCat.extendScalars φ).obj (K.homology i) ≅
            (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj K).homology i,
          (ModuleCat.extendScalars φ).map (K.homologyπ i) ≫ e.hom =
            (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj K).liftCycles
              ((ModuleCat.extendScalars φ).map (K.iCycles i)) _ rfl
              (map_iCycles_d _ K i _) ≫
            (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj K).homologyπ i) ∧
    (∀ [IsDomain R] [ValuationRing R],
      Module.Finite R (LinearMap.ker (K.d 0 1).hom) ∧ Module.Free R (LinearMap.ker (K.d 0 1).hom) ∧
      (∃ N : Submodule R (K.X 0), IsCompl (LinearMap.ker (K.d 0 1).hom) N) ∧
      Bijective (LinearMap.tensorKer (FractionRing R) (FractionRing R) (K.d 0 1).hom) ∧
      Injective (LinearMap.tensorKer (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R)
        (K.d 0 1).hom)) :=
  ⟨fun i _ => finite_homology_extendScalars K i _,
    upperSemicontinuous_finrank_homology_fiber K,
    isLocallyConstant_sum_range_finrank_homology_fiber K n hn,
    fun i _ h => grauert_homology K i h,
    ker_free_of_valuationRing (FractionRing R) _⟩

example : UpperSemicontinuous fun p : PrimeSpectrum ℤ => finrank p.asIdeal.ResidueField
    (LinearMap.ker ((0 : ℤ →ₗ[ℤ] ℤ).baseChange p.asIdeal.ResidueField) ⧸
      (LinearMap.range ((LinearMap.lsmul ℤ ℤ 2).baseChange p.asIdeal.ResidueField)).submoduleOf
        (LinearMap.ker ((0 : ℤ →ₗ[ℤ] ℤ).baseChange p.asIdeal.ResidueField))) :=
  upperSemicontinuous_finrank_linearMap_homology _ _ (LinearMap.zero_comp _)

end Main

end GlobalTheory
