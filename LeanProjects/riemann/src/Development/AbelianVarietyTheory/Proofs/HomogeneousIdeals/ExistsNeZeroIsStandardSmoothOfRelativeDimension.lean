import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsApplyEqZeroAndEqOne
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HasAlgebraicChartsOfIsStandardSmooth
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import ReciprocityTheory.SemistableReduction.AeBlockSphereEvalNeZero

namespace GlobalTheory.AffinePoints

open Topology Filter Set MvPolynomial MeasureTheory Module
open scoped Manifold ContDiff

section Null

theorem addHaar_image_eq_zero_of_finrank_lt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]
    (h : finrank ℝ E < finrank ℝ F) {s : Set E} {f : E → F} (hf : DifferentiableOn ℝ f s) :
    μ (f '' s) = 0 := by
  obtain ⟨i, hi⟩ := finrank_le_iff_exists_linearMap.1 h.le
  obtain ⟨L, hL⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hi)
  have hsurj : Function.Surjective L := fun x => ⟨i x, DFunLike.congr_fun hL x⟩
  have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt h
  let L' : F →L[ℝ] E := LinearMap.toContinuousLinearMap L
  have him : f '' s = (f ∘ L') '' (L' ⁻¹' s) := by
    rw [image_comp, image_preimage_eq s (f := L') hsurj]
  rw [him]
  refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
    (f' := fun x => (fderivWithin ℝ f s (L' x)).comp L') (fun x hx => ?_) (fun x _ => ?_)
  · exact (hf _ hx).hasFDerivWithinAt.comp x L'.hasFDerivWithinAt (mapsTo_preimage _ _)
  · refine LinearMap.det_eq_zero_iff_ker_ne_bot.2 fun h0 => hker (le_bot_iff.1 ?_)
    rw [← h0]
    intro v hv
    have : L' v = 0 := hv
    simp [this]

variable {d : ℕ}

theorem volume_image_eq_zero_of_finrank_lt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (h : finrank ℂ E < d) {s : Set E} {f : E → Fin d → ℂ}
    (hf : DifferentiableOn ℂ f s) : volume (f '' s) = 0 := by
  refine addHaar_image_eq_zero_of_finrank_lt volume ?_ (hf.restrictScalars ℝ)
  rw [finrank_real_of_complex, finrank_real_of_complex]
  simpa using h

theorem volume_range_eq_zero_of_mdifferentiable {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [LindelofSpace M]
    (h : finrank ℂ E < d) {f : M → Fin d → ℂ} (hf : MDifferentiable I 𝓘(ℂ, Fin d → ℂ) f) :
    volume (range f) = 0 := by
  obtain ⟨t, htc, ht⟩ := countable_cover_nhds (U := fun x : M => (extChartAt I x).source)
    fun x => extChartAt_source_mem_nhds x
  have : range f ⊆ ⋃ x ∈ t, (f ∘ (extChartAt I x).symm) '' (extChartAt I x).target := by
    rintro _ ⟨m, rfl⟩
    obtain ⟨x, hx, hm⟩ := mem_iUnion₂.1 (ht.symm ▸ mem_univ m)
    exact mem_iUnion₂.2 ⟨x, hx, extChartAt I x m, (extChartAt I x).map_source hm, by
      rw [Function.comp_apply, (extChartAt I x).left_inv hm]⟩
  refine measure_mono_null this ((measure_biUnion_null_iff htc).2 fun x _ => ?_)
  exact volume_image_eq_zero_of_finrank_lt h (mdifferentiableOn_iff_differentiableOn.1
    (hf.comp_mdifferentiableOn mdifferentiableOn_extChartAt_symm))

end Null

section Algebra

universe u

variable {K A : Type u} [Field K] [CommRing A] [Algebra K A] {d : ℕ}

theorem exists_finite_injective_of_ringKrullDim_eq [Algebra.FiniteType K A]
    (hd : ringKrullDim A = d) :
    ∃ g : MvPolynomial (Fin d) K →ₐ[K] A, Function.Injective g ∧ g.Finite := by
  haveI : Nontrivial A := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hd
    exact WithBot.bot_ne_natCast _ hd
  obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg K A
  letI := g.toRingHom.toAlgebra
  haveI : FaithfulSMul (MvPolynomial (Fin s) K) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) A := ⟨RingHom.Finite.to_isIntegral hfin⟩
  rw [ringKrullDim_eq_of_isIntegral (MvPolynomial (Fin s) K) A,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at hd
  obtain rfl : s = d := by simpa using hd
  exact ⟨g, hg, hfin⟩

theorem faithfulSMul_and_isAlgebraic_of_etale (R S : Type*) [CommRing R] [IsDomain R] [CommRing S]
    [IsDomain S] [Algebra R S] [Algebra.Etale R S] :
    FaithfulSMul R S ∧ Algebra.IsAlgebraic R S := by
  haveI : FaithfulSMul R S := inferInstance
  exact ⟨this, isAlgebraic_of_quasiFiniteAt R S ⊥⟩

theorem trdeg_eq_of_etale [IsDomain A] (g : MvPolynomial (Fin d) K →ₐ[K] A) (hg : g.Etale) :
    Algebra.trdeg K A = d := by
  letI : Algebra (MvPolynomial (Fin d) K) A := g.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin d) K) A := hg
  haveI : IsScalarTower K (MvPolynomial (Fin d) K) A :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  obtain ⟨_, _⟩ := faithfulSMul_and_isAlgebraic_of_etale (MvPolynomial (Fin d) K) A
  rw [trdeg_eq_of_isAlgebraic_top K (MvPolynomial (Fin d) K) A, MvPolynomial.trdeg_of_isDomain]
  simp

theorem ringKrullDim_eq_of_isStandardSmooth [IsDomain A]
    [Algebra.IsStandardSmoothOfRelativeDimension d K A] : ringKrullDim A = d := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial d K A
  haveI := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (R := K) (S := A) d
  exact ringKrullDim_eq_of_trdeg_eq K A (trdeg_eq_of_etale g hg)

theorem exists_notMem_isStandardSmoothOfRelativeDimension [IsDomain A] [Algebra.FiniteType K A]
    (hd : ringKrullDim A = d) (P : Ideal A) [P.IsPrime] [Algebra.IsSmoothAt K P] :
    ∃ s ∉ P, Algebra.IsStandardSmoothOfRelativeDimension d K (Localization.Away s) := by
  haveI : Algebra.FinitePresentation K A := Algebra.FinitePresentation.of_finiteType.1 ‹_›
  obtain ⟨s, hs, ι, σ, _, _, ⟨Q⟩⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth K P
  refine ⟨s, hs, ?_⟩
  have hs0 : Submonoid.powers s ≤ nonZeroDivisors A :=
    powers_le_nonZeroDivisors_of_noZeroDivisors fun h => hs (h ▸ P.zero_mem)
  haveI : IsDomain (Localization.Away s) := IsLocalization.isDomain_localization hs0
  haveI H : Algebra.IsStandardSmoothOfRelativeDimension Q.dimension K (Localization.Away s) :=
    Q.isStandardSmoothOfRelativeDimension rfl
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    Q.dimension K (Localization.Away s)
  have h1 := trdeg_eq_of_etale g hg
  haveI : FaithfulSMul A (Localization.Away s) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsLocalization.injective _ hs0)
  haveI : Algebra.IsAlgebraic A (Localization.Away s) :=
    IsLocalization.isAlgebraic _ (Submonoid.powers s)
  rw [trdeg_eq_of_isAlgebraic_top K A (Localization.Away s)] at h1
  have h2 := ringKrullDim_eq_of_trdeg_eq K A h1
  rw [hd] at h2
  obtain rfl : d = Q.dimension := by exact_mod_cast h2
  exact H

theorem exists_ne_zero_isStandardSmoothOfRelativeDimension [PerfectField K] [IsDomain A]
    [Algebra.FiniteType K A] (hd : ringKrullDim A = d) :
    ∃ s : A, s ≠ 0 ∧ Algebra.IsStandardSmoothOfRelativeDimension d K (Localization.Away s) := by
  haveI : Algebra.IsSmoothAt K (⊥ : Ideal A) := by
    haveI : IsLocalization (⊥ : Ideal A).primeCompl (FractionRing A) := by
      rw [Ideal.primeCompl_bot]; infer_instance
    let e := (IsLocalization.algEquiv (⊥ : Ideal A).primeCompl (FractionRing A)
      (Localization.AtPrime (⊥ : Ideal A))).restrictScalars K
    haveI : Algebra.EssFiniteType K (FractionRing A) := .comp K A _
    haveI : Algebra.FormallySmooth K (FractionRing A) := Algebra.FormallySmooth.of_perfectField
    exact Algebra.FormallySmooth.of_equiv e
  simpa using exists_notMem_isStandardSmoothOfRelativeDimension (K := K) hd ⊥

end Algebra

variable {A : Type} [CommRing A] [Algebra ℂ A] {d : ℕ}

theorem volume_coords_image_zeroSet [IsDomain A] (g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A)
    (hg : @Algebra.IsAlgebraic _ A _ _ g.toRingHom.toAlgebra) {f : A} (hf : f ≠ 0) :
    volume (coords g '' {p : A →ₐ[ℂ] ℂ | p f = 0}) = 0 := by
  letI : Algebra (MvPolynomial (Fin d) ℂ) A := g.toRingHom.toAlgebra
  obtain ⟨r, hr, c, hc⟩ := (hg.isAlgebraic f).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hf)
  refine measure_mono_null ?_ (ReciprocityTheory.MultiplicativeHeights.ae_eval_ne_zero_of_ne_zero_fin d r hr)
  rintro _ ⟨p, hp, rfl⟩
  have h1 : eval (coords g p) r = p (g r) := aeval_coords g p r
  have h2 : g r = f * c := hc
  simp only [mem_compl_iff, mem_setOf_eq, not_not]
  rw [h1, h2, map_mul, hp, zero_mul]

theorem volume_coords_image_zeroSet_of_etale [IsDomain A] (g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A)
    (hg : g.Etale) {f : A} (hf : f ≠ 0) :
    volume (coords g '' {p : A →ₐ[ℂ] ℂ | p f = 0}) = 0 := by
  letI : Algebra (MvPolynomial (Fin d) ℂ) A := g.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin d) ℂ) A := hg
  exact volume_coords_image_zeroSet g (faithfulSMul_and_isAlgebraic_of_etale _ A).2 hf

theorem isProperMap_coords (g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (hg : g.Finite) :
    IsProperMap (coords g : (A →ₐ[ℂ] ℂ) → Fin d → ℂ) :=
  (mvPolynomialHomeomorph ℂ ℂ (Fin d)).isProperMap.comp
    (isProperMap_comap g (RingHom.Finite.to_isIntegral hg))

theorem surjective_coords (g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (hg : g.Finite)
    (hinj : Function.Injective g) : Function.Surjective (coords g : (A →ₐ[ℂ] ℂ) → Fin d → ℂ) :=
  (mvPolynomialHomeomorph ℂ ℂ (Fin d)).surjective.comp
    (surjective_comap_of_isIntegral g (RingHom.Finite.to_isIntegral hg) hinj)

theorem isOpenMap_coords [IsDomain A] (g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (hg : g.Finite)
    (hinj : Function.Injective g) : IsOpenMap (coords g : (A →ₐ[ℂ] ℂ) → Fin d → ℂ) :=
  (mvPolynomialHomeomorph ℂ ℂ (Fin d)).isOpenMap.comp (isOpenMap_comap g hg hinj)

theorem dense_compl_of_volume_coords_image [IsDomain A] (g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A)
    (hg : g.Finite) (hinj : Function.Injective g) {S : Set (A →ₐ[ℂ] ℂ)}
    (hS : volume (coords g '' S) = 0) : Dense Sᶜ := by
  have h1 : Dense (coords g '' S)ᶜ :=
    Measure.dense_of_ae (μ := volume) (measure_eq_zero_iff_ae_notMem.1 hS)
  refine (h1.preimage (isOpenMap_coords g hg hinj)).mono ?_
  intro p hp hpS
  exact hp ⟨p, hpS, rfl⟩

theorem dense_nonvanishing [IsDomain A] [Algebra.FiniteType ℂ A] {f : A} (hf : f ≠ 0) :
    Dense {p : A →ₐ[ℂ] ℂ | p f ≠ 0} := by
  obtain ⟨s, g, hinj, hg⟩ := exists_finite_inj_algHom_of_fg ℂ A
  refine dense_compl_of_volume_coords_image g hg hinj (volume_coords_image_zeroSet g ?_ hf)
  letI := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin s) ℂ) A := hg
  infer_instance

theorem interior_zeroSet_eq_empty [IsDomain A] [Algebra.FiniteType ℂ A] {f : A} (hf : f ≠ 0) :
    interior {p : A →ₐ[ℂ] ℂ | p f = 0} = ∅ :=
  interior_eq_empty_iff_dense_compl.2 (dense_nonvanishing hf)

theorem IsAlgebraicChart.volume_image_zeroSet [IsDomain A] [Algebra.FiniteType ℂ A]
    (hd : ringKrullDim A = d) {e : OpenPartialHomeomorph (A →ₐ[ℂ] ℂ) (Fin d → ℂ)}
    (he : IsAlgebraicChart e) {f : A} (hf : f ≠ 0) :
    volume (e '' (e.source ∩ {p | p f = 0})) = 0 := by
  obtain ⟨x, s, hx⟩ := he.exists_eq_div
  by_cases hs : s = 0
  · have : e.source = ∅ := eq_empty_of_forall_notMem fun p hp => (hx p hp).1 (by simp [hs])
    simp [this]
  have hs0 : Submonoid.powers s ≤ nonZeroDivisors A :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hs
  let B := Localization.Away s
  haveI : IsDomain B := IsLocalization.isDomain_localization hs0
  have hAB : Function.Injective (algebraMap A B) := IsLocalization.injective _ hs0
  let g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] B :=
    aeval fun i => algebraMap A B (x i) * IsLocalization.Away.invSelf s
  have hsub : e '' (e.source ∩ {p | p f = 0}) ⊆
      coords g '' {q : B →ₐ[ℂ] ℂ | q (algebraMap A B f) = 0} := by
    rintro _ ⟨p, ⟨hp, hpf⟩, rfl⟩
    obtain ⟨q, rfl⟩ : p ∈ range (comap (IsScalarTower.toAlgHom ℂ A B)) := by
      rw [range_comap_away s]; exact (hx p hp).1
    refine ⟨q, hpf, funext fun i => ?_⟩
    rw [(hx _ hp).2 i]
    refine apply_eq_div_of_mul_eq q (IsLocalization.Away.algebraMap_isUnit s) ?_
    simp only [g, aeval_X]
    rw [mul_assoc, mul_comm _ (algebraMap A B s), IsLocalization.Away.mul_invSelf, mul_one]
  refine measure_mono_null hsub ?_
  by_cases hinj : Function.Injective g
  · refine volume_coords_image_zeroSet g ?_ ((map_ne_zero_iff _ hAB).2 hf)
    letI : Algebra (MvPolynomial (Fin d) ℂ) B := g.toRingHom.toAlgebra
    haveI : IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) B :=
      IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
    haveI : FaithfulSMul (MvPolynomial (Fin d) ℂ) B :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
    haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective _ _).mpr hAB
    haveI : Algebra.IsAlgebraic A B := IsLocalization.isAlgebraic _ (Submonoid.powers s)
    obtain ⟨n, h1, h2⟩ := exists_ringKrullDim_eq_and_trdeg_eq ℂ A
    rw [hd] at h1
    obtain rfl : d = n := by exact_mod_cast h1
    have h3 := trdeg_add_eq ℂ (MvPolynomial (Fin d) ℂ) (A := B)
    rw [trdeg_eq_of_isAlgebraic_top ℂ A B, h2, MvPolynomial.trdeg_of_isDomain] at h3
    simp only [Cardinal.mk_fintype, Fintype.card_fin, Cardinal.lift_natCast] at h3
    have h4 : Algebra.trdeg (MvPolynomial (Fin d) ℂ) B = 0 :=
      Cardinal.eq_of_add_eq_add_left (h3.trans (add_zero _).symm) (Cardinal.natCast_lt_aleph0)
    exact trdeg_eq_zero_iff.1 h4
  · rw [injective_iff_map_eq_zero] at hinj
    push Not at hinj
    obtain ⟨r, hr0, hr⟩ := hinj
    refine measure_mono_null ?_ (ReciprocityTheory.MultiplicativeHeights.ae_eval_ne_zero_of_ne_zero_fin d r hr)
    rintro _ ⟨p, -, rfl⟩
    have h1 : eval (coords g p) r = p (g r) := aeval_coords g p r
    simp only [mem_compl_iff, mem_setOf_eq, not_not]
    rw [h1, hr0, map_zero]

theorem exists_isAlgebraicChart_of_isSmoothAt [IsDomain A] [Algebra.FiniteType ℂ A]
    (hd : ringKrullDim A = d) (p : A →ₐ[ℂ] ℂ)
    (hp : haveI := RingHom.ker_isPrime p; Algebra.IsSmoothAt ℂ (RingHom.ker p)) :
    ∃ e : OpenPartialHomeomorph (A →ₐ[ℂ] ℂ) (Fin d → ℂ), IsAlgebraicChart e ∧ p ∈ e.source := by
  haveI := RingHom.ker_isPrime p
  obtain ⟨s, hs, H⟩ := exists_notMem_isStandardSmoothOfRelativeDimension (K := ℂ) hd
    (RingHom.ker p)
  exact exists_isAlgebraicChart_of_away s (Localization.Away s) p hs

theorem hasAlgebraicCharts_of_smooth [IsDomain A] [Algebra.Smooth ℂ A]
    (hd : ringKrullDim A = d) : HasAlgebraicCharts ℂ A d := fun p =>
  exists_isAlgebraicChart_of_isSmoothAt hd p inferInstance

section Cover

variable {ι : Type*} [Countable ι] {E H M : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℂ (E i)] [∀ i, FiniteDimensional ℂ (E i)] [∀ i, TopologicalSpace (H i)]
  {I : ∀ i, ModelWithCorners ℂ (E i) (H i)} [∀ i, TopologicalSpace (M i)]
  [∀ i, ChartedSpace (H i) (M i)] [∀ i, IsManifold (I i) 1 (M i)] [∀ i, LindelofSpace (M i)]

theorem volume_coords_image_iUnion_range (g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A)
    (hE : ∀ i, finrank ℂ (E i) < d) (φ : ∀ i, M i → (A →ₐ[ℂ] ℂ))
    (hφ : ∀ i a, MDifferentiable (I i) 𝓘(ℂ) fun m => φ i m a) :
    volume (coords g '' ⋃ i, range (φ i)) = 0 := by
  rw [image_iUnion]
  refine measure_iUnion_null fun i => ?_
  rw [← range_comp]
  exact volume_range_eq_zero_of_mdifferentiable (I := I i) (hE i) fun m =>
    mdifferentiableAt_pi_of_forall fun j => hφ i _ m

theorem iUnion_range_ne_univ [Algebra.FiniteType ℂ A] (hd : ringKrullDim A = d)
    (hE : ∀ i, finrank ℂ (E i) < d) (φ : ∀ i, M i → (A →ₐ[ℂ] ℂ))
    (hφ : ∀ i a, MDifferentiable (I i) 𝓘(ℂ) fun m => φ i m a) : ⋃ i, range (φ i) ≠ univ := by
  obtain ⟨g, hinj, hg⟩ := exists_finite_injective_of_ringKrullDim_eq (K := ℂ) hd
  intro h
  have := volume_coords_image_iUnion_range g hE φ hφ
  rw [h, image_univ, (surjective_coords g hg hinj).range_eq] at this
  exact (isOpen_univ.measure_ne_zero volume univ_nonempty) this

theorem dense_compl_iUnion_range [IsDomain A] [Algebra.FiniteType ℂ A] (hd : ringKrullDim A = d)
    (hE : ∀ i, finrank ℂ (E i) < d) (φ : ∀ i, M i → (A →ₐ[ℂ] ℂ))
    (hφ : ∀ i a, MDifferentiable (I i) 𝓘(ℂ) fun m => φ i m a) : Dense (⋃ i, range (φ i))ᶜ := by
  obtain ⟨g, hinj, hg⟩ := exists_finite_injective_of_ringKrullDim_eq (K := ℂ) hd
  exact dense_compl_of_volume_coords_image g hg hinj (volume_coords_image_iUnion_range g hE φ hφ)

end Cover

section Immersion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} {φ : E → (A →ₐ[ℂ] ℂ)}

theorem fderiv_apply_mul {z : E} (hφ : ∀ a, DifferentiableAt ℂ (fun z => φ z a) z) (v : E)
    (a b : A) : fderiv ℂ (fun z => φ z (a * b)) z v =
      φ z a * fderiv ℂ (fun z => φ z b) z v + φ z b * fderiv ℂ (fun z => φ z a) z v := by
  simp only [map_mul]
  rw [fderiv_fun_mul (hφ a) (hφ b)]
  simp

theorem fderiv_apply_add {z : E} (hφ : ∀ a, DifferentiableAt ℂ (fun z => φ z a) z) (v : E)
    (a b : A) : fderiv ℂ (fun z => φ z (a + b)) z v =
      fderiv ℂ (fun z => φ z a) z v + fderiv ℂ (fun z => φ z b) z v := by
  simp only [map_add]
  rw [fderiv_fun_add (hφ a) (hφ b)]
  simp

theorem fderiv_apply_eq_zero_of_mem_adjoin {z : E}
    (hφ : ∀ a, DifferentiableAt ℂ (fun z => φ z a) z) (v : E) {s : Set A}
    (hs : ∀ a ∈ s, fderiv ℂ (fun z => φ z a) z v = 0) {a : A} (ha : a ∈ Algebra.adjoin ℂ s) :
    fderiv ℂ (fun z => φ z a) z v = 0 := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha => exact hs a ha
  | algebraMap c => simp
  | add a b _ _ ha hb => rw [fderiv_apply_add hφ, ha, hb, add_zero]
  | mul a b _ _ ha hb => rw [fderiv_apply_mul hφ, ha, hb]; simp

theorem fderiv_apply_eval₂ {R : Type*} [CommRing R] (g : R →+* A) {z : E}
    (hφ : ∀ a, DifferentiableAt ℂ (fun z => φ z a) z) (v : E)
    (hv : ∀ r, fderiv ℂ (fun z => φ z (g r)) z v = 0) (a : A) (h : Polynomial R) :
    fderiv ℂ (fun z => φ z (h.eval₂ g a)) z v =
      φ z ((Polynomial.derivative h).eval₂ g a) * fderiv ℂ (fun z => φ z a) z v := by
  induction h using Polynomial.induction_on with
  | C r => simpa using hv r
  | add P Q hP hQ =>
    rw [Polynomial.eval₂_add, fderiv_apply_add hφ, hP, hQ]
    simp [add_mul]
  | monomial n r ih =>
    rw [pow_succ, ← mul_assoc, Polynomial.eval₂_mul, Polynomial.eval₂_X, fderiv_apply_mul hφ, ih,
      Polynomial.derivative_mul (g := Polynomial.X), Polynomial.derivative_X, Polynomial.eval₂_add,
      Polynomial.eval₂_mul _ _ (p := Polynomial.derivative _), Polynomial.eval₂_X, mul_one]
    simp only [map_add, map_mul]
    ring

theorem exists_isOpen_fderiv_eq_zero {R : Type*} [CommRing R] (g : R →+* A) {a : A}
    (ha : g.IsIntegralElem a) (hU : IsOpen U) (hne : U.Nonempty)
    (hφ : ∀ a, DifferentiableOn ℂ (fun z => φ z a) U) :
    ∃ V ⊆ U, IsOpen V ∧ V.Nonempty ∧ ∀ z ∈ V, ∀ v,
      (∀ r, fderiv ℂ (fun z => φ z (g r)) z v = 0) → fderiv ℂ (fun z => φ z a) z v = 0 := by
  obtain ⟨h, hm, hh⟩ := ha
  let c : ℕ → A := fun k => (Polynomial.derivative^[k] h).eval₂ g a
  obtain ⟨k, hk, z₀, hz₀, hk'⟩ : ∃ k, (∀ z ∈ U, φ z (c k) = 0) ∧ ∃ z ∈ U, φ z (c (k + 1)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ k, ∀ z ∈ U, φ z (c k) = 0 := by
      intro k
      induction k with
      | zero => intro z _; simp [c, hh]
      | succ k ih => exact hcon k ih
    obtain ⟨z, hz⟩ := hne
    have h1 := hall h.natDegree z hz
    have h2 : Polynomial.derivative^[h.natDegree] h = Polynomial.C (h.natDegree.factorial : R) := by
      rw [Polynomial.eq_C_of_natDegree_le_zero (p := Polynomial.derivative^[h.natDegree] h)
        ((Polynomial.natDegree_iterate_derivative h _).trans (by simp)),
        Polynomial.coeff_iterate_derivative, zero_add, Nat.descFactorial_self,
        hm.coeff_natDegree, nsmul_eq_mul, mul_one]
    simp [c, h2, Nat.factorial_ne_zero] at h1
  refine ⟨U ∩ (fun z => φ z (c (k + 1))) ⁻¹' {0}ᶜ, inter_subset_left,
    (hφ _).continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton, ⟨z₀, hz₀, hk'⟩,
    fun z hz v hv => ?_⟩
  have h1 := fderiv_apply_eval₂ g (fun a => (hφ a).differentiableAt (hU.mem_nhds hz.1)) v hv a
    (Polynomial.derivative^[k] h)
  have h2 : (fun z => φ z (c k)) =ᶠ[𝓝 z] fun _ => 0 := by
    filter_upwards [hU.mem_nhds hz.1] with w hw using hk w hw
  rw [← Function.iterate_succ_apply' Polynomial.derivative] at h1
  rw [show (fun z => φ z ((Polynomial.derivative^[k] h).eval₂ g a)) = fun z => φ z (c k) from rfl,
    h2.fderiv_eq] at h1
  simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.zero_apply] at h1
  exact (mul_eq_zero.1 h1.symm).resolve_left hz.2

theorem rank_le_of_immersion [Algebra.FiniteType ℂ A] (hd : ringKrullDim A = d)
    (hU : IsOpen U) (hne : U.Nonempty) (hφ : ∀ a, DifferentiableOn ℂ (fun z => φ z a) U)
    (himm : ∀ z ∈ U, ∀ v, (∀ a, fderiv ℂ (fun z => φ z a) z v = 0) → v = 0) :
    Module.rank ℂ E ≤ d := by
  classical
  obtain ⟨g, -, hg⟩ := exists_finite_injective_of_ringKrullDim_eq (K := ℂ) hd
  have hint : g.toRingHom.IsIntegral := RingHom.Finite.to_isIntegral hg
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType ℂ A).out
  have key : ∀ t : Finset A, ∃ V ⊆ U, IsOpen V ∧ V.Nonempty ∧ ∀ z ∈ V, ∀ v,
      (∀ r, fderiv ℂ (fun z => φ z (g r)) z v = 0) →
        ∀ a ∈ t, fderiv ℂ (fun z => φ z a) z v = 0 := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨U, subset_rfl, hU, hne, by simp⟩
    | insert a t _ ih =>
      obtain ⟨V, hVU, hV, hVne, H⟩ := ih
      obtain ⟨W, hWV, hW, hWne, H'⟩ := exists_isOpen_fderiv_eq_zero (φ := φ) g.toRingHom (hint a)
        hV hVne fun a => (hφ a).mono hVU
      refine ⟨W, hWV.trans hVU, hW, hWne, fun z hz v hv b hb => ?_⟩
      rcases Finset.mem_insert.1 hb with rfl | hb
      · exact H' z hz v hv
      · exact H z (hWV hz) v hv b hb
  obtain ⟨V, hVU, -, ⟨z, hz⟩, H⟩ := key s
  have hd' : ∀ a, DifferentiableAt ℂ (fun z => φ z a) z := fun a =>
    (hφ a).differentiableAt (hU.mem_nhds (hVU hz))
  let L : E →ₗ[ℂ] (Fin d → ℂ) :=
    LinearMap.pi fun i => (fderiv ℂ (fun z => φ z (g (X i))) z : E →ₗ[ℂ] ℂ)
  have hL : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    refine himm z (hVU hz) v fun a => fderiv_apply_eq_zero_of_mem_adjoin hd' v
      (H z hz v fun r => ?_) (hs ▸ Algebra.mem_top)
    refine fderiv_apply_eq_zero_of_mem_adjoin hd' v (s := range fun i => g (X i)) ?_ ?_
    · rintro _ ⟨i, rfl⟩
      exact congrFun hv i
    · rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨r, (DFunLike.congr_fun (MvPolynomial.aeval_unique g) r).symm⟩
  simpa using L.lift_rank_le_of_injective hL

end Immersion

theorem complexPoints_manifold_and_dimension (A : Type) [CommRing A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] (d : ℕ) :
    (∀ g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A, g.Etale →
      IsLocalHomeomorph (coords g : (A →ₐ[ℂ] ℂ) → Fin d → ℂ) ∧
      ∀ p : A →ₐ[ℂ] ℂ, ∃ e : OpenPartialHomeomorph (A →ₐ[ℂ] ℂ) (Fin d → ℂ), p ∈ e.source ∧
        (e : (A →ₐ[ℂ] ℂ) → Fin d → ℂ) = coords g ∧
        ∀ a, AnalyticOnNhd ℂ (fun z => e.symm z a) e.target) ∧
    (Algebra.IsStandardSmoothOfRelativeDimension d ℂ A →
      (∃ g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A, g.Etale) ∧
      ∃ h : HasAlgebraicCharts ℂ A d,
        letI := h.chartedSpace
        IsManifold 𝓘(ℂ, Fin d → ℂ) ω (A →ₐ[ℂ] ℂ) ∧
          ∀ a : A, ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ω fun p : A →ₐ[ℂ] ℂ => p a) ∧
    (IsDomain A → ringKrullDim A = d →
      (∀ f : A, f ≠ 0 →
        IsClosed {p : A →ₐ[ℂ] ℂ | p f = 0} ∧ interior {p : A →ₐ[ℂ] ℂ | p f = 0} = ∅ ∧
        (∀ g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A, g.Etale →
          volume (coords g '' {p : A →ₐ[ℂ] ℂ | p f = 0}) = 0) ∧
        ∀ e : OpenPartialHomeomorph (A →ₐ[ℂ] ℂ) (Fin d → ℂ), IsAlgebraicChart e →
          volume (e '' (e.source ∩ {p | p f = 0})) = 0) ∧
      ∀ (ι : Type) [Countable ι] (E H M : ι → Type) [∀ i, NormedAddCommGroup (E i)]
        [∀ i, NormedSpace ℂ (E i)] [∀ i, FiniteDimensional ℂ (E i)] [∀ i, TopologicalSpace (H i)]
        (I : ∀ i, ModelWithCorners ℂ (E i) (H i)) [∀ i, TopologicalSpace (M i)]
        [∀ i, ChartedSpace (H i) (M i)] [∀ i, IsManifold (I i) 1 (M i)] [∀ i, LindelofSpace (M i)]
        (φ : ∀ i, M i → (A →ₐ[ℂ] ℂ)), (∀ i, finrank ℂ (E i) < d) →
        (∀ i a, MDifferentiable (I i) 𝓘(ℂ) fun m => φ i m a) →
        ⋃ i, range (φ i) ≠ univ ∧ Dense (⋃ i, range (φ i))ᶜ) := by
  refine ⟨fun g hg => ⟨isLocalHomeomorph_coords_of_etale g hg, exists_chart_of_etale g hg⟩,
    fun _ => ⟨Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial d ℂ A,
      hasAlgebraicCharts_of_isStandardSmooth, HasAlgebraicCharts.isManifold _,
      HasAlgebraicCharts.contMDiff_eval _⟩,
    fun _ hd => ⟨fun f hf => ⟨isClosed_zeroSet f, interior_zeroSet_eq_empty hf,
      fun g hg => volume_coords_image_zeroSet_of_etale g hg hf,
      fun e he => he.volume_image_zeroSet hd hf⟩, ?_⟩⟩
  intro ι _ E H M _ _ _ _ I _ _ _ _ φ hE hφ
  exact ⟨iUnion_range_ne_univ hd hE φ hφ, dense_compl_iUnion_range hd hE φ hφ⟩

end GlobalTheory.AffinePoints
