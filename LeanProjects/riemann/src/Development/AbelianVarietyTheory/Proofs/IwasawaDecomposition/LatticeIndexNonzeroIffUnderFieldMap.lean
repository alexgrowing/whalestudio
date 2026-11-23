import Mathlib
import Formalism.QuotientMetricDivisors.Statement
import Formalism.HermitianLattices.StatementLat
import Formalism.LocalRingCardinality.Lemmas
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapSpanBaseChangeEquivSubmoduleOf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthBaseChangeQuotientOfMapMaximalIdeal

open NumberField IsDedekindDomain IsLocalRing TensorProduct

namespace GlobalTheory.LidxBaseChange

theorem length_eq_of_residue (R O M : Type*) [CommRing R] [CommRing O] [IsLocalRing O] [Algebra R O]
    [AddCommGroup M] [Module R M] [Module O M] [IsScalarTower R O M]
    (h1 : Module.length R (ResidueField O) = 1) : Module.length R M = Module.length O M := by
  have step : ∀ {p q : Submodule O M}, p ⋖ q → Module.length R q = Module.length R p + 1 := by
    intro p q h
    let f : p →ₗ[O] q := Submodule.inclusion h.le
    have key : IsSimpleModule O (q ⧸ f.range) := by
      rwa [Submodule.range_inclusion, ← covBy_iff_quot_is_simple h.le]
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp key
    rw [eq_maximalIdeal hm] at e
    let g : q →ₗ[O] ResidueField O := e.comp f.range.mkQ
    have : Function.Injective f := Submodule.inclusion_injective _
    have : Function.Surjective g := e.surjective.comp f.range.mkQ_surjective
    have : Function.Exact f g := LinearMap.exact_iff.mpr ((e.ker_comp f.range.mkQ).trans f.range.ker_mkQ)
    rw [Module.length_eq_add_of_exact (f.restrictScalars R) (g.restrictScalars R)
      (by simpa) (by simpa) (by simpa), h1]
  by_cases h : IsFiniteLength O M
  · obtain ⟨s, hs_bot, hs_top⟩ := isFiniteLength_iff_exists_compositionSeries.mp h
    rw [← Module.length_compositionSeries s hs_bot hs_top]
    suffices ∀ k, Module.length R (s k) = k by
      rw [← Fin.val_last s.length, ← this, ← RelSeries.last, hs_top]
      exact Module.length_top.symm
    intro k
    induction k using Fin.induction with
    | zero => rw [← RelSeries.head, hs_bot]; simp
    | succ i hi => simpa [hi] using step (s.step i)
  · have : ¬ IsFiniteLength R M := by
      contrapose! h
      rw [isFiniteLength_iff_isNoetherian_isArtinian] at h ⊢
      exact h.imp (isNoetherian_of_tower R) (isArtinian_of_tower R)
    rw [← Module.length_ne_top_iff, not_ne_iff] at h this
    rw [h, this]

theorem length_residue_atPrime {R : Type*} [CommRing R] (P : Ideal R) [P.IsMaximal] :
    Module.length R (ResidueField (Localization.AtPrime P)) = 1 := by
  rw [Module.length_eq_of_surjective (S := R) (R := ResidueField (Localization.AtPrime P))
    (Ideal.algebraMap_residueField_surjective P)]
  simp

theorem mem_localization_iff {R W : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] [AddCommGroup W] [Module R W]
    [Module (Localization.AtPrime P) W] [IsScalarTower R (Localization.AtPrime P) W] (X : Submodule R W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ P X ↔ x ∈ Submodule.span (Localization.AtPrime P) (X : Set W) := by
  constructor
  · rintro ⟨s, hs, hx⟩
    obtain ⟨u, hu⟩ := IsLocalization.map_units (Localization.AtPrime P) (⟨s, hs⟩ : P.primeCompl)
    have : x = (↑u⁻¹ : Localization.AtPrime P) • (s • x) := by
      rw [← algebraMap_smul (Localization.AtPrime P) s x]
      change x = _ • (algebraMap R (Localization.AtPrime P) ((⟨s, hs⟩ : P.primeCompl) : R)) • x
      rw [← hu, smul_smul, Units.inv_mul, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hx)
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact ⟨1, P.primeCompl.one_mem, by simpa using hy⟩
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      obtain ⟨s, hs, hy⟩ := hy
      obtain ⟨⟨a, t⟩, h⟩ := IsLocalization.surj P.primeCompl c
      refine ⟨s * t, P.primeCompl.mul_mem hs t.2, ?_⟩
      have : (s * (t : R)) • c • y = a • s • y := by
        rw [mul_smul, ← algebraMap_smul (Localization.AtPrime P) (t : R), smul_smul _ c, mul_comm _ c]
        dsimp only at h
        rw [h, algebraMap_smul, smul_comm]
      rw [this]
      exact X.smul_mem a hy

theorem length_localized_eq₂ {R W : Type*} [CommRing R] (P : Ideal R) [P.IsMaximal] [AddCommGroup W] [Module R W]
    [Module (Localization.AtPrime P) W] [IsScalarTower R (Localization.AtPrime P) W] (X Y : Submodule R W) :
    Module.length R (↥(Formalism.HermitianLatticesTheory.localization₂ P X) ⧸ (Formalism.HermitianLatticesTheory.localization₂ P Y).comap (Formalism.HermitianLatticesTheory.localization₂ P X).subtype) =
      Module.length (Localization.AtPrime P) (↥(Submodule.span (Localization.AtPrime P) (X : Set W)) ⧸
        (Submodule.span (Localization.AtPrime P) (Y : Set W)).comap
          (Submodule.span (Localization.AtPrime P) (X : Set W)).subtype) := by
  rw [← length_eq_of_residue R _ _ (length_residue_atPrime P)]
  have hX : Formalism.HermitianLatticesTheory.localization₂ P X = (Submodule.span (Localization.AtPrime P) (X : Set W)).restrictScalars R :=
    Submodule.ext fun x => mem_localization_iff P X x
  have hY : Formalism.HermitianLatticesTheory.localization₂ P Y = (Submodule.span (Localization.AtPrime P) (Y : Set W)).restrictScalars R :=
    Submodule.ext fun x => mem_localization_iff P Y x
  rw [hX, hY]
  exact (Submodule.Quotient.restrictScalarsEquiv R ((Submodule.span (Localization.AtPrime P) (Y : Set W)).comap
          (Submodule.span (Localization.AtPrime P) (X : Set W)).subtype)).length_eq

theorem span_image_inf {A O V W : Type*} [CommRing A] [CommRing O] [Algebra A O] [Module.Flat A O]
    [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W] [Module O W] [IsScalarTower A O W]
    (φ : V →ₗ[A] W) (h : Function.Injective (φ.liftBaseChange O)) (M N : Submodule A V) :
    Submodule.span O (φ '' (M : Set V)) ⊓ Submodule.span O (φ '' (N : Set V)) =
      Submodule.span O (φ '' ((M ⊓ N : Submodule A V) : Set V)) := by
  have key : ∀ X : Submodule A V,
      Submodule.span O (φ '' (X : Set V)) = (X.baseChange O).map (φ.liftBaseChange O) := fun X => by
    rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, Set.image_image]
    congr 1
    exact Set.image_congr fun v _ => by simp
  rw [key, key, key, baseChange_inf, Submodule.map_inf _ h]

theorem exists_lidx_eq_mul (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    {d d' : ℕ} (ψ : (Fin d → K) →ₗ[K] (Fin d' → K')) (hψ : LinearIndependent K' (ψ ∘ Pi.basisFun K (Fin d)))
    (P : HeightOneSpectrum (𝓞 K)) (P' : HeightOneSpectrum (𝓞 K')) [P'.asIdeal.LiesOver P.asIdeal] :
    ∃ e : ℕ, 0 < e ∧ ∀ A B : Submodule (𝓞 K) (Fin d → K),
      Formalism.HermitianLatticesTheory.lidx P'.asIdeal (Submodule.span (𝓞 K') (ψ '' (A : Set (Fin d → K))))
        (Submodule.span (𝓞 K') (ψ '' (B : Set (Fin d → K)))) = Formalism.HermitianLatticesTheory.lidx P.asIdeal A B * e := by
  have hPm := P.isMaximal
  have hPm' := P'.isMaximal
  let O := Localization.AtPrime P.asIdeal
  let O' := Localization.AtPrime P'.asIdeal
  letI : Algebra O K := IsLocalization.localizationAlgebraOfSubmonoidLe O K P.asIdeal.primeCompl
    (nonZeroDivisors (𝓞 K)) P.asIdeal.primeCompl_le_nonZeroDivisors
  have : IsScalarTower (𝓞 K) O K := IsLocalization.localization_isScalarTower_of_submonoid_le O K _ _ _
  letI : Algebra O' K' := IsLocalization.localizationAlgebraOfSubmonoidLe O' K' P'.asIdeal.primeCompl
    (nonZeroDivisors (𝓞 K')) P'.asIdeal.primeCompl_le_nonZeroDivisors
  have : IsScalarTower (𝓞 K') O' K' := IsLocalization.localization_isScalarTower_of_submonoid_le O' K' _ _ _
  have : IsFractionRing O K := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.asIdeal.primeCompl O K
  have : IsFractionRing O' K' :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P'.asIdeal.primeCompl O' K'
  have : IsScalarTower (𝓞 K) O' K' := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 K') O', ← IsScalarTower.algebraMap_apply (𝓞 K') O' K',
      ← IsScalarTower.algebraMap_apply]
  letI : Algebra O O' := Localization.AtPrime.algebraOfLiesOver P.asIdeal P'.asIdeal
  have : Localization.AtPrime.IsLiesOverAlgebra P.asIdeal P'.asIdeal := ⟨rfl⟩
  have : IsScalarTower (𝓞 K) O O' := inferInstance
  have : IsLocalHom (algebraMap O O') := inferInstance
  have : IsDiscreteValuationRing O :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) P.ne_bot _
  have : IsDiscreteValuationRing O' :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K') P'.ne_bot _
  have : FaithfulSMul O O' := inferInstance
  have : Module.Flat O O' := inferInstance
  have : IsLocalHom (algebraMap O O) := inferInstance
  refine ⟨(maximalIdeal O').ramificationIdx O, ramificationIdx_maximalIdeal_pos O O', ?_⟩
  have hlen : ∀ M N : Submodule (𝓞 K) (Fin d → K), N ≤ M →
      Formalism.HermitianLatticesTheory.locLen P'.asIdeal (Submodule.span (𝓞 K') (ψ '' (M : Set (Fin d → K))))
        (Submodule.span (𝓞 K') (ψ '' (N : Set (Fin d → K)))) =
        Formalism.HermitianLatticesTheory.locLen P.asIdeal M N * (maximalIdeal O').ramificationIdx O := by
    intro M N hNM
    unfold Formalism.HermitianLatticesTheory.locLen
    rw [length_localized_eq₂, length_localized_eq₂, Submodule.span_span_of_tower, Submodule.span_span_of_tower]
    have h1 := Formalism.BasicNotions.FBC.length_flat_tower P.asIdeal (IsFractionRing.injective O' K') ψ _ hψ N M hNM
    have h2 := Formalism.BasicNotions.FBC.length_flat_tower P.asIdeal (IsFractionRing.injective O K)
      (LinearMap.id : (Fin d → K) →ₗ[K] (Fin d → K)) (Pi.basisFun K (Fin d))
      (Pi.basisFun K (Fin d)).linearIndependent N M hNM
    rw [length_fibre_eq_ramificationIdx O O'] at h1
    have h3 : Module.length O (O ⧸ (maximalIdeal O).map (algebraMap O O)) = 1 := by
      rw [Algebra.algebraMap_self, Ideal.map_id]
      have h4 := IsDiscreteValuationRing.length_quotient_pow_maximalIdeal O 1
      rw [pow_one] at h4
      exact_mod_cast h4
    rw [h3, mul_one, LinearMap.id_coe, Set.image_id, Set.image_id] at h2
    rw [h1, h2, ENat.toNat_mul, ENat.toNat_coe]
  intro A B
  have hinj := Formalism.BasicNotions.FBC.liftBaseChange_injective_top (A := 𝓞 K) (IsFractionRing.injective (𝓞 K') K') ψ _ hψ
  have hinf := span_image_inf _ hinj A B
  unfold Formalism.HermitianLatticesTheory.lidx
  erw [hinf]
  erw [hlen A _ inf_le_left, hlen B _ inf_le_right]
  push_cast
  ring

theorem lidx_ne_zero_iff : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (φ : K →+* K') (d d' : ℕ) (G : Matrix (Fin d') (Fin d) K'),
  Function.Bijective G.mulVec → ∀ (P : HeightOneSpectrum (𝓞 K)) (P' : HeightOneSpectrum (𝓞 K')),
  (∀ (x : 𝓞 K) (x' : 𝓞 K'), φ (x : K) = (x' : K') → (x ∈ P.asIdeal ↔ x' ∈ P'.asIdeal)) →
  ∀ A B : Submodule (𝓞 K) (Fin d → K), A.FG → B.FG →
    (Formalism.HermitianLatticesTheory.lidx P.asIdeal A B ≠ 0 ↔ Formalism.HermitianLatticesTheory.lidx P'.asIdeal
      (Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) '' (A : Set (Fin d → K))))
      (Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) '' (B : Set (Fin d → K)))) ≠ 0) := by
  intro K K' _ _ _ _ φ d d' G hG P P' hP A B _ _
  letI : Algebra K K' := φ.toAlgebra
  have : P'.asIdeal.LiesOver P.asIdeal := ⟨Ideal.ext fun x => hP x (algebraMap (𝓞 K) (𝓞 K') x) rfl⟩
  let ψ : (Fin d → K) →ₗ[K] (Fin d' → K') :=
    (G.mulVecLin.restrictScalars K) ∘ₗ (Algebra.linearMap K K').compLeft (Fin d)
  have hψ : LinearIndependent K' (ψ ∘ Pi.basisFun K (Fin d)) := by
    have h := (Pi.basisFun K' (Fin d)).linearIndependent.map' G.mulVecLin (LinearMap.ker_eq_bot.2 hG.1)
    have e : ψ ∘ Pi.basisFun K (Fin d) = G.mulVecLin ∘ Pi.basisFun K' (Fin d) := by
      funext i
      simp only [ψ, Function.comp_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
      congr 1
      funext k
      by_cases hk : k = i <;> simp [hk, Pi.single_apply]
    rw [e]
    exact h
  obtain ⟨e, he, h⟩ := exists_lidx_eq_mul K K' ψ hψ P P'
  have h' := h A B
  have hf : (fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) = ψ := rfl
  rw [hf, h']
  simp [he.ne']

end GlobalTheory.LidxBaseChange
