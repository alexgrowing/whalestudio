import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField

noncomputable section

theorem isIntegral_of_map {F F' : Type*} [Field F] [Field F'] (j : F →+* F') {x : F}
    (h : IsIntegral ℤ (j x)) : IsIntegral ℤ x :=
  (isIntegral_algHom_iff j.toIntAlgHom j.injective).1 h

theorem le_of_map_le {F F' : Type*} [Field F] [NumberField F] [Field F'] [NumberField F']
    (j : F →+* F') {A B : Ideal (𝓞 F)} (hB : B ≠ ⊥)
    (h : A.map (RingOfIntegers.mapRingHom j) ≤ B.map (RingOfIntegers.mapRingHom j)) : A ≤ B := by
  obtain ⟨b, hbB, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hB
  obtain ⟨B', hB'⟩ : B ∣ Ideal.span {b} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hbB)
  have hB'0 : B' ≠ 0 := by
    rintro rfl
    rw [mul_zero, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at hB'
    exact hb0 hB'
  have key : A * B' ≤ B * B' := by
    rw [← hB', Ideal.mul_le]
    intro x hx y hy
    have hm : RingOfIntegers.mapRingHom j (x * y) ∈
        (Ideal.span {b}).map (RingOfIntegers.mapRingHom j) := by
      rw [hB', Ideal.map_mul, map_mul]
      exact Ideal.mul_mem_mul (h (Ideal.mem_map_of_mem _ hx)) (Ideal.mem_map_of_mem _ hy)
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hm
    obtain ⟨z, hz⟩ := hm
    have hbF : (b : F) ≠ 0 := by
      intro h0
      exact hb0 (RingOfIntegers.ext (by simpa using h0))
    have hz' : (z : F') * j (b : F) = j ((x * y : 𝓞 F) : F) := by
      have := congrArg (fun t : 𝓞 F' ↦ (t : F')) hz
      simpa using this
    have himg : j (((x * y : 𝓞 F) : F) / (b : F)) = (z : F') := by
      rw [map_div₀, ← hz', mul_div_assoc, div_self ((map_ne_zero j).2 hbF), mul_one]
    have hq : IsIntegral ℤ (((x * y : 𝓞 F) : F) / (b : F)) := by
      apply isIntegral_of_map j
      rw [himg]
      exact RingOfIntegers.isIntegral_coe z
    rw [Ideal.mem_span_singleton']
    refine ⟨⟨_, hq⟩, RingOfIntegers.ext ?_⟩
    show ((x * y : 𝓞 F) : F) / (b : F) * (b : F) = ((x * y : 𝓞 F) : F)
    rw [div_mul_cancel₀ _ hbF]
  have hdvd : B * B' ∣ A * B' := Ideal.dvd_iff_le.2 key
  exact Ideal.dvd_iff_le.1 ((mul_dvd_mul_iff_right hB'0).1 hdvd)

theorem eq_of_map_eq {F F' : Type*} [Field F] [NumberField F] [Field F'] [NumberField F']
    (j : F →+* F') {A B : Ideal (𝓞 F)} (hB : B ≠ ⊥)
    (h : A.map (RingOfIntegers.mapRingHom j) = B.map (RingOfIntegers.mapRingHom j)) : A = B := by
  have hA : A ≠ ⊥ := by
    rintro rfl
    rw [Ideal.map_bot, eq_comm, Ideal.map_eq_bot_iff_of_injective] at h
    · exact hB h
    · intro x y hxy
      exact RingOfIntegers.ext (j.injective (by simpa using congrArg (fun t : 𝓞 F' ↦ (t : F')) hxy))
  exact le_antisymm (le_of_map_le j hB h.le) (le_of_map_le j hA h.ge)

theorem exists_extension_mem_range {F : Type} [Field F] [NumberField F] (τ : F →+* ℂ) {z₁ z₂ : ℂ}
    (h₁ : IsAlgebraic ℚ z₁) (h₂ : IsAlgebraic ℚ z₂) :
    ∃ (F' : Type) (_ : Field F') (_ : NumberField F') (j : F →+* F') (τ' : F' →+* ℂ),
      τ'.comp j = τ ∧ z₁ ∈ Set.range τ' ∧ z₂ ∈ Set.range τ' := by
  let e := AlgEquiv.ofInjectiveField τ.toRatAlgHom
  let E₁ : IntermediateField ℚ ℂ := τ.toRatAlgHom.fieldRange
  let E₂ : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {z₁, z₂}
  have : FiniteDimensional ℚ E₁ := LinearEquiv.finiteDimensional e.toLinearEquiv
  have : FiniteDimensional ℚ E₂ :=
    IntermediateField.finiteDimensional_adjoin_pair h₁.isIntegral h₂.isIntegral
  have : FiniteDimensional ℚ ↥(E₁ ⊔ E₂) := IntermediateField.finiteDimensional_sup E₁ E₂
  have : NumberField ↥(E₁ ⊔ E₂) := NumberField.of_module_finite ℚ _
  refine ⟨↥(E₁ ⊔ E₂), inferInstance, inferInstance,
    ((IntermediateField.inclusion (le_sup_left : E₁ ≤ E₁ ⊔ E₂)).toRingHom.comp e.toRingEquiv.toRingHom),
    (E₁ ⊔ E₂).val.toRingHom, ?_, ?_, ?_⟩
  · ext x
    rfl
  · exact ⟨⟨z₁, (le_sup_right : E₂ ≤ E₁ ⊔ E₂)
      (IntermediateField.subset_adjoin ℚ _ (by simp))⟩, rfl⟩
  · exact ⟨⟨z₂, (le_sup_right : E₂ ≤ E₁ ⊔ E₂)
      (IntermediateField.subset_adjoin ℚ _ (by simp))⟩, rfl⟩

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
