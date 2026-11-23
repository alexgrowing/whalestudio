import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAbelianTotallyRealExtPrescribedCompletionStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AbOverSubfield

theorem exists_place_between {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω]
    [Algebra F K] [Algebra K Ω] [Algebra F Ω] [IsScalarTower F K Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 K), IsPlaceOver A w := by
  have hint : ∀ x : 𝓞 K, algebraMap K Ω (x : K) ∈ A := fun x => by
    have h : IsIntegral A (algebraMap K Ω (x : K)) :=
      (x.isIntegral_coe.map (algebraMap K Ω).toIntAlgHom).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hy]
    exact y.2
  let f : 𝓞 K →+* A := ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)).codRestrict A hint
  let P : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hu : v.asIdeal = P.comap (algebraMap (𝓞 F) (𝓞 K)) := by
    ext x
    rw [← hA x, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply F K Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨P, inferInstance, hne⟩, hP⟩

theorem exists_avoid {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hvT : v ∉ T) :
    ∃ c : 𝓞 F, c ∉ v.asIdeal ∧ ∀ u ∈ T, c ∈ u.asIdeal := by
  classical
  have : ∀ u ∈ T, ∃ a : 𝓞 F, a ∈ u.asIdeal ∧ a ∉ v.asIdeal := by
    intro u hu
    by_contra hc
    push_neg at hc
    have hle : u.asIdeal ≤ v.asIdeal := hc
    have := u.isMaximal.eq_of_le v.isPrime.ne_top hle
    exact hvT (HeightOneSpectrum.ext this ▸ hu)
  choose! a ha using this
  refine ⟨∏ u ∈ T, a u, ?_, fun u hu => ?_⟩
  · intro hmem
    obtain ⟨u, hu, hau⟩ := (Ideal.IsPrime.prod_mem_iff (hp := v.isPrime)).1 hmem
    exact (ha u hu).2 hau
  · rw [← Finset.mul_prod_erase T a hu]
    exact Ideal.mul_mem_right _ _ (ha u hu).1

end GlobalTheory.AbOverSubfield

namespace GlobalTheory.AbOverSubfield

theorem exists_abelian_over_subfield : ∀ (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (h : IsPlaceOver A v) (T : Finset (HeightOneSpectrum (𝓞 F))), v ∉ T → ∀ F₁ : IntermediateField F Ω, FiniteDimensional F F₁ → (∀ φ : F₁ →+* ℂ, ComplexEmbedding.IsReal φ) → ∀ V : Subgroup (G F Ω), IsOpen (V : Set (G F Ω)) → ⁅Dec (F := F) A ⊓ F₁.fixingSubgroup, Dec (F := F) A ⊓ F₁.fixingSubgroup⁆ ≤ V → ∃ F₂ : IntermediateField F Ω, F₁ ≤ F₂ ∧ FiniteDimensional F F₂ ∧ ⁅F₁.fixingSubgroup, F₁.fixingSubgroup⁆ ≤ F₂.fixingSubgroup ∧ (∀ φ : F₂ →+* ℂ, ComplexEmbedding.IsReal φ) ∧ Dec (F := F) A ⊓ F₂.fixingSubgroup ≤ V ∧ ∀ u ∈ T, ∀ A' : ValuationSubring Ω, IsPlaceOver A' u → Dec (F := F) A' ⊓ F₁.fixingSubgroup ≤ F₂.fixingSubgroup := by
  intro Ω _ F _ _ _ _ A v h T hvT F₁ hF₁ hre V hV hcomm
  haveI : NumberField F₁ := NumberField.of_module_finite F F₁
  haveI : Algebra.IsAlgebraic F₁ Ω := Algebra.IsAlgebraic.tower_top (K := F) F₁
  haveI : IsAlgClosure F₁ Ω := ⟨IsAlgClosure.isAlgClosed F, inferInstance⟩
  haveI : IsTotallyReal F₁ := ⟨fun w => NumberField.InfinitePlace.isReal_iff.2 (hre _)⟩
  let ρ : (Ω ≃ₐ[F₁] Ω) →* (Ω ≃ₐ[F] Ω) := AlgEquiv.restrictScalarsHom F
  have hρdec : ∀ (B : ValuationSubring Ω) (g : Ω ≃ₐ[F₁] Ω), ρ g ∈ Dec (F := F) B ↔ g ∈ Dec (F := F₁) B :=
    fun _ _ => Iff.rfl
  have hρfix : ∀ g, ρ g ∈ F₁.fixingSubgroup := fun g => by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact g.commutes ⟨x, hx⟩

  have hlift : ∀ g ∈ F₁.fixingSubgroup, ∃ g' : Ω ≃ₐ[F₁] Ω, ρ g' = g := fun g hg =>
    ⟨IntermediateField.fixingSubgroupEquiv F₁ ⟨g, hg⟩, by ext x; rfl⟩
  obtain ⟨v₁, hv₁⟩ := exists_place_between (K := F₁) h
  obtain ⟨c, hcv, hcT⟩ := exists_avoid v T hvT
  set c₁ : 𝓞 F₁ := algebraMap (𝓞 F) (𝓞 F₁) c with hc₁
  have hc₁val : ∀ (B : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 F₁)), IsPlaceOver B w →
      (c₁ ∈ w.asIdeal ↔ B.valuation (algebraMap F Ω (c : F)) < 1) := by
    intro B w hw
    rw [← hw, IsScalarTower.algebraMap_apply F F₁ Ω]
    rfl
  have hc0 : c₁ ≠ 0 := by
    intro h0
    apply hcv
    have : c = 0 := (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 F₁)) (by rw [← hc₁, h0, map_zero])
    rw [this]; exact v.asIdeal.zero_mem
  have hfin : {w : HeightOneSpectrum (𝓞 F₁) | c₁ ∈ w.asIdeal}.Finite :=
    (Ideal.finite_factors (I := Ideal.span {c₁}) (by simpa using hc0)).subset
      fun w hw => Ideal.dvd_span_singleton.mpr hw
  set T₁ := hfin.toFinset
  have hv₁T : v₁ ∉ T₁ := by
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, hc₁val A v₁ hv₁, h]
    exact hcv
  let V₁ : Subgroup (Dec (F := F₁) A) := (V.comap ρ).comap (Dec (F := F₁) A).subtype
  have hV₁ : IsOpen (V₁ : Set (Dec (F := F₁) A)) := by
    obtain ⟨E, hE, hEV⟩ := (krullTopology_mem_nhds_one_iff F Ω (V : Set (G F Ω))).1 (hV.mem_nhds V.one_mem)
    haveI : FiniteDimensional F (E ⊔ F₁ : IntermediateField F Ω) := IntermediateField.finiteDimensional_sup _ _
    let E₁ : IntermediateField F₁ Ω := IntermediateField.extendScalars (le_sup_right : F₁ ≤ E ⊔ F₁)
    haveI : FiniteDimensional F E₁ := (inferInstance : FiniteDimensional F (E ⊔ F₁ : IntermediateField F Ω))
    haveI : FiniteDimensional F₁ E₁ := FiniteDimensional.right F F₁ _
    refine Subgroup.isOpen_mono (H₁ := (E₁.fixingSubgroup).comap (Dec (F := F₁) A).subtype) ?_
      ((E₁.fixingSubgroup_isOpen).preimage continuous_subtype_val)
    intro g hg
    simp only [V₁, Subgroup.mem_comap]
    apply hEV
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [Subgroup.mem_comap, IntermediateField.mem_fixingSubgroup_iff] at hg
    exact hg x ((IntermediateField.mem_extendScalars _).2 (le_sup_left (a := E) hx))
  have hcomm₁ : commutator (Dec (F := F₁) A) ≤ V₁ := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    simp only [V₁, Subgroup.mem_comap, map_commutatorElement]
    apply hcomm
    exact Subgroup.commutator_mem_commutator ⟨(hρdec A _).2 g₁.2, hρfix _⟩ ⟨(hρdec A _).2 g₂.2, hρfix _⟩
  obtain ⟨F₂', hfin₂, hab, hreal₂, hiff, hsplit⟩ := GlobalTheory.T.exists_abelian_totallyReal_ext_prescribedCompletion Ω F₁ A v₁ hv₁ V₁ hV₁ hcomm₁ T₁ hv₁T
  have hcomm₂ : commutator (Ω ≃ₐ[F₁] Ω) ≤ F₂'.fixingSubgroup := by
    rw [← F₂'.restrictNormalHom_ker, commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact IsMulCommutative.is_comm.comm _ _
  have hfix₂ : ∀ g : Ω ≃ₐ[F₁] Ω, ρ g ∈ (F₂'.restrictScalars F).fixingSubgroup ↔ g ∈ F₂'.fixingSubgroup :=
    fun _ => Iff.rfl
  have hle : F₁ ≤ F₂'.restrictScalars F := by
    intro x hx
    show x ∈ F₂'
    simpa using F₂'.algebraMap_mem ⟨x, hx⟩
  refine ⟨F₂'.restrictScalars F, hle, ?_, ?_, ?_, ?_, ?_⟩
  · exact FiniteDimensional.trans F F₁ F₂'
  · rw [Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    obtain ⟨g₁', rfl⟩ := hlift g₁ h₁
    obtain ⟨g₂', rfl⟩ := hlift g₂ h₂
    rw [← map_commutatorElement, hfix₂]
    exact hcomm₂ (by rw [commutator_def]; exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  · intro φ
    exact hreal₂ φ
  · rintro g ⟨hgA, hg₂⟩
    have hg₁ : g ∈ F₁.fixingSubgroup := by
      have hg₂' : g ∈ (F₂'.restrictScalars F).fixingSubgroup := hg₂
      rw [IntermediateField.mem_fixingSubgroup_iff] at hg₂' ⊢
      intro x hx
      exact hg₂' x (hle hx)
    obtain ⟨g', rfl⟩ := hlift g hg₁
    have := (hiff ⟨g', (hρdec A g').1 hgA⟩).1 ((hfix₂ g').1 hg₂)
    exact this
  · intro u hu A' hA' g ⟨hgA, hg₁⟩
    obtain ⟨g', rfl⟩ := hlift g hg₁
    obtain ⟨w', hw'⟩ := exists_place_between (K := F₁) hA'
    have hw'T : w' ∈ T₁ := by
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, hc₁val A' w' hw', hA']
      exact hcT u hu
    exact (hfix₂ g').2 (hsplit w' hw'T A' hw' ((hρdec A' g').1 hgA))

end GlobalTheory.AbOverSubfield
