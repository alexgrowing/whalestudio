import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CongruenceNumberRankThree

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N

namespace UpperTheory.V.Af

theorem continuous_restrictScalarsHom (F E Ω : Type) [Field F] [Field E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω]
    [IsScalarTower F E Ω] : Continuous (AlgEquiv.restrictScalarsHom F : G E Ω →* G F Ω) := by
  apply continuous_of_continuousAt_one
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨M, hM, hMs⟩ := hs
  let b := Module.finBasis F M
  set t : Set Ω := Set.range (fun i => ((b i : M) : Ω)) with ht_def
  have hMt : M ≤ IntermediateField.adjoin F t := by
    intro m hm
    have h := congrArg (fun y : M => (y : Ω)) (b.sum_repr ⟨m, hm⟩)
    simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at h
    rw [← h]
    exact sum_mem fun i _ => IntermediateField.smul_mem _
      (IntermediateField.subset_adjoin F t (Set.mem_range_self i))
  have hint : ∀ x ∈ t, IsIntegral E x := by
    rintro x ⟨i, rfl⟩
    have : IsIntegral F (b i) := IsIntegral.of_finite F _
    exact (IsIntegral.map (IsScalarTower.toAlgHom F M Ω) this).tower_top
  haveI : Finite t := Set.finite_range _
  haveI : FiniteDimensional E (IntermediateField.adjoin E t) :=
    IntermediateField.finiteDimensional_adjoin hint
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  refine ⟨IntermediateField.adjoin E t, inferInstance, fun σ hσ => hMs ?_⟩
  have hH : IntermediateField.adjoin F t ≤ IntermediateField.fixedField
      (Subgroup.map (AlgEquiv.restrictScalarsHom F (A := Ω) (S := E))
        (IntermediateField.adjoin E t).fixingSubgroup) := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    rintro f ⟨τ, hτ, rfl⟩
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ x
      (IntermediateField.subset_adjoin E _ hx)
  exact IntermediateField.fixingSubgroup_antitone hMt
    ((IntermediateField.le_iff_le _ _).1 hH ⟨σ, hσ, rfl⟩)

section Iso

variable {F₀ F₁ Ω : Type} [Field F₀] [Field F₁] [Field Ω] [Algebra F₀ F₁] [Algebra F₀ Ω] [Algebra F₁ Ω]
  [IsScalarTower F₀ F₁ Ω]

theorem restrictScalarsHom_surjective (h : Function.Surjective (algebraMap F₀ F₁)) :
    Function.Surjective (AlgEquiv.restrictScalarsHom F₀ : G F₁ Ω →* G F₀ Ω) := fun σ =>
  ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x => by
    obtain ⟨y, rfl⟩ := h x
    rw [← IsScalarTower.algebraMap_apply]
    exact σ.commutes y, rfl⟩

theorem IsAdOf.of_surjective (h : Function.Surjective (algebraMap F₀ F₁)) {F k : Type} [Field F] [Algebra F₀ F] [Algebra F₁ F]
    [Algebra F Ω] [IsScalarTower F₀ F Ω] [IsScalarTower F₁ F Ω] [Field k] {n : ℕ} {r : G F Ω →* GL (Fin n) k}
    {μ : G F Ω →* kˣ} {ρ : Representation k (G F₀ Ω) (Matrix (Fin n) (Fin n) k)} (H : IsAdOf r μ ρ) :
    IsAdOf (F₀ := F₁) r μ (ρ.comp (AlgEquiv.restrictScalarsHom F₀ : G F₁ Ω →* G F₀ Ω)) := by
  obtain ⟨c, P, hj, h1, h2, h3⟩ := H
  obtain ⟨c', rfl⟩ := restrictScalarsHom_surjective (Ω := Ω) h c
  refine ⟨c', P, hj, fun s s' e => h1 s s' ?_, fun s X => h2 s X, h3⟩
  exact AlgEquiv.ext fun x => AlgEquiv.congr_fun e x

variable [NumberField F₀] [NumberField F₁] {l : ℕ} [Fact l.Prime]
  {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V]

theorem IsBK.of_surjective (h : Function.Surjective (algebraMap F₀ F₁)) {ρ : Representation C (G F₀ Ω) V} {c : G F₀ Ω → V}
    (H : IsBK l ρ c) :
    IsBK l (ρ.comp (AlgEquiv.restrictScalarsHom F₀ : G F₁ Ω →* G F₀ Ω)) fun s => c (s.restrictScalars F₀) := by
  constructor
  · intro w hw
    obtain ⟨A, hA, x, hx⟩ := H.away (w.under (𝓞 F₀)) fun h' => hw (by simpa using Ideal.mem_comap.1 h')
    refine ⟨A, fun y => ?_, x, fun s hs => hx _ ⟨hs.1, hs.2⟩⟩
    obtain ⟨z, hz⟩ := h (y : F₁)
    have hi : IsIntegral ℤ z := by
      rw [← isIntegral_algebraMap_iff (algebraMap F₀ F₁).injective, hz]
      exact y.2
    have e : y = algebraMap (𝓞 F₀) (𝓞 F₁) ⟨z, hi⟩ := Subtype.ext hz.symm
    have := hA ⟨z, hi⟩
    rw [← hz, ← IsScalarTower.algebraMap_apply, e]
    exact this
  · intro τ
    obtain ⟨j, hj, ⟨hc, hm⟩, x, hx⟩ := H.above (τ.comp (algebraMap F₀ F₁))
    let φ : ↥(decJ F₁ j) →* ↥(decJ F₀ j) :=
      { toFun := fun g => ⟨(g.1.1.restrictScalars F₀, g.1.2), g.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hφ : Continuous φ := Continuous.subtype_mk
      (((continuous_restrictScalarsHom F₀ F₁ Ω).comp (continuous_fst.comp continuous_subtype_val)).prodMk
        (continuous_snd.comp continuous_subtype_val)) _
    refine ⟨j, RingHom.ext fun y => ?_, ⟨hc.comp hφ, fun g g' => hm (φ g) (φ g')⟩, x, fun g => hx (φ g)⟩
    obtain ⟨z, rfl⟩ := h y
    rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
    exact RingHom.congr_fun hj z

theorem BlochKatoSelmerVanishes.of_surjective (h : Function.Surjective (algebraMap F₀ F₁)) {ρ : Representation C (G F₀ Ω) V}
    (H : BlochKatoSelmerVanishes l (ρ.comp (AlgEquiv.restrictScalarsHom F₀ : G F₁ Ω →* G F₀ Ω))) : BlochKatoSelmerVanishes l ρ := by
  intro c hc hbk
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 (H _
    ⟨hc.1.comp (continuous_restrictScalarsHom F₀ F₁ Ω), fun g g' => hc.2 (g.restrictScalars F₀) (g'.restrictScalars F₀)⟩
    (hbk.of_surjective h))
  refine (mem_coboundaries1 _ _).2 ⟨m, fun g => ?_⟩
  obtain ⟨g', rfl⟩ := restrictScalarsHom_surjective (Ω := Ω) h g
  exact hm g'

end Iso

theorem surjective_algebraMap_real (K : Type) [Field K] [NumberField K] [IsCMField K] (h : Module.finrank ℚ K = 2) :
    Function.Surjective (algebraMap ℚ (maximalRealSubfield K)) := by
  have h1 := Module.finrank_mul_finrank ℚ (maximalRealSubfield K) K
  rw [h, Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield K) K] at h1
  have h2 : Module.finrank ℚ (maximalRealSubfield K) = 1 := by omega
  exact ((Algebra.finrank_eq_one_iff_bijective_algebraMap).1 h2).2

end UpperTheory.V.Af
