import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem real_eq_one_of_nonneg_of_mul_self_eq_one (x : ℝ) (h0 : 0 ≤ x) (h : x * x = 1) : x = 1 := by
  nlinarith

theorem UpperTheory.V.FW.realGen :
    ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (x : Cl K), Function.Surjective (IsCMField.unitsMulComplexConjInv K) → x ∈ minK (clMap (cE K)) → ∃ (I : (Ideal (𝓞 K))⁰) (a : 𝓞 K), ClassGroup.mk0 I = x ∧ a ≠ 0 ∧ cE K (a : K) = a ∧ (I * idMap (cE K) I).1 = Ideal.span {a} := by
  intro K _ _ _ x hsurj hx
  set σ := RingOfIntegers.mapRingEquiv (cE K) with hσdef
  have hσK : ∀ y : 𝓞 K, ((σ y : 𝓞 K) : K) = cE K (y : K) := fun y => rfl
  have hσσ : ∀ y : 𝓞 K, σ (σ y) = y := fun y => by
    apply RingOfIntegers.ext
    rw [hσK, hσK]
    exact IsCMField.complexConj_apply_apply K (y : K)
  have hw : ∀ (w : InfinitePlace K) (y : 𝓞 K), w (σ y : K) = w (y : K) := fun w y =>
    IsCMField.infinitePlace_complexConj K w (y : K)
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective x
  set J := idMap (cE K) I with hJdef
  have hJ : (J : Ideal (𝓞 K)) = Ideal.map σ (I : Ideal (𝓞 K)) := rfl
  have hmapmap : ∀ A : Ideal (𝓞 K), Ideal.map σ (Ideal.map σ A) = A := by
    intro A
    show Ideal.map (σ : 𝓞 K →+* 𝓞 K) (Ideal.map (σ : 𝓞 K →+* 𝓞 K) A) = A
    rw [Ideal.map_map]
    have : (σ : 𝓞 K →+* 𝓞 K).comp (σ : 𝓞 K →+* 𝓞 K) = RingHom.id _ :=
      RingHom.ext fun y => hσσ y
    rw [this, Ideal.map_id]
  have hJJ : Ideal.map σ (J : Ideal (𝓞 K)) = I := by
    rw [hJ, hmapmap]
  have hprin : Submodule.IsPrincipal ((I * J : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) := by
    rw [← ClassGroup.mk0_eq_one_iff (I * J).2]
    have := hx
    simp only [minK, MonoidHom.mem_ker, MonoidHom.mul_apply, class_map_mk0, MonoidHom.id_apply] at this
    rw [← map_mul, mul_comm] at this
    exact this
  obtain ⟨b, hb⟩ := hprin
  have hb' : ((I * J : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = Ideal.span {b} := hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at hb'
    exact nonZeroDivisors.coe_ne_zero (I * J) hb'
  have hspan : Ideal.span {σ b} = Ideal.span {b} := by
    rw [← Set.image_singleton, ← Ideal.map_span, ← hb', Submonoid.coe_mul, Ideal.map_mul, ← hJ,
      hJJ, mul_comm]
  obtain ⟨t, ht⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  have hσt : σ (t : 𝓞 K) * t = 1 := by
    have h1 := congrArg σ ht
    rw [map_mul, hσσ] at h1
    have : b * (σ t * t) = b * 1 := by
      rw [← mul_assoc, h1, ht, mul_one]
    exact mul_left_cancel₀ hb0 this
  have htor : t⁻¹ ∈ Units.torsion K := by
    refine inv_mem ?_
    rw [Units.mem_torsion]
    intro w
    show w ((t : 𝓞 K) : K) = 1
    have hK : ((σ t : 𝓞 K) : K) * ((t : 𝓞 K) : K) = 1 := by
      exact_mod_cast congrArg (fun y : 𝓞 K => (y : K)) hσt
    have hprod := congrArg w hK
    rw [map_mul, map_one, hw] at hprod
    exact real_eq_one_of_nonneg_of_mul_self_eq_one _ (AbsoluteValue.nonneg _ _) hprod
  obtain ⟨v, hv⟩ := hsurj ⟨t⁻¹, htor⟩
  have hv2 : v * ((IsCMField.unitsComplexConj K) v)⁻¹ = t⁻¹ := by
    have hv1 := congrArg Subtype.val hv
    rw [IsCMField.unitsMulComplexConjInv_apply] at hv1
    exact hv1
  rw [mul_inv_eq_iff_eq_mul] at hv2
  have hv' : (v : 𝓞 K) = ((t⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * σ v := by
    have h3 := congrArg Units.val hv2
    rw [Units.val_mul] at h3
    exact h3
  have hσb : σ b = b * ((t⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by
    calc σ b = σ b * t * ((t⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by rw [mul_assoc, Units.mul_inv, mul_one]
      _ = b * ((t⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by rw [ht]
  refine ⟨I, b * v, rfl, mul_ne_zero hb0 v.ne_zero, ?_, ?_⟩
  · rw [← hσK]
    congr 1
    rw [map_mul, hσb, mul_assoc, ← hv']
  · rw [Ideal.span_singleton_mul_right_unit v.isUnit]
    exact hb'
