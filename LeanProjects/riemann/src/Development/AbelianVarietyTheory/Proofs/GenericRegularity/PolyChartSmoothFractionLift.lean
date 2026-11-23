import Mathlib

namespace GlobalTheory

open MvPolynomial

section PolyChart

variable {K F₀ : Type} (V : Type) [Field K] [Field F₀] [Algebra K F₀] (R₀ : Subalgebra K F₀)

noncomputable def polyChartHom :
    MvPolynomial V R₀ →ₐ[K] FractionRing (MvPolynomial V F₀) :=
  (IsScalarTower.toAlgHom K (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀))).comp
    (MvPolynomial.mapAlgHom R₀.val)

theorem polyChartHom_apply (p : MvPolynomial V R₀) :
    polyChartHom V R₀ p = algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀))
      (MvPolynomial.map (R₀.val : R₀ →+* F₀) p) := rfl

theorem polyChartHom_injective : Function.Injective (polyChartHom V R₀) := by
  intro p q h
  rw [polyChartHom_apply, polyChartHom_apply] at h
  exact MvPolynomial.map_injective _ Subtype.val_injective
    (IsFractionRing.injective (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) h)

theorem polyChartHom_C (a : R₀) :
    polyChartHom V R₀ (C a) = algebraMap F₀ (FractionRing (MvPolynomial V F₀)) a := by
  rw [polyChartHom_apply, MvPolynomial.map_C,
    IsScalarTower.algebraMap_apply F₀ (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀))]
  rfl

theorem polyChartHom_X (v : V) :
    polyChartHom V R₀ (X v) =
      algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) (X v) := by
  rw [polyChartHom_apply, MvPolynomial.map_X]

theorem polyChartHom_range :
    (polyChartHom V R₀).range = Algebra.adjoin K
      ((algebraMap F₀ (FractionRing (MvPolynomial V F₀))) '' (R₀ : Set F₀) ∪
        Set.range fun v : V =>
          algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) (X v)) := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    change polyChartHom V R₀ p ∈ _
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [polyChartHom_C]
      exact Algebra.subset_adjoin (Or.inl ⟨a, a.2, rfl⟩)
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p v hp =>
      rw [map_mul, polyChartHom_X]
      exact mul_mem hp (Algebra.subset_adjoin (Or.inr ⟨v, rfl⟩))
  · rw [Algebra.adjoin_le_iff]
    rintro _ (⟨a, ha, rfl⟩ | ⟨v, rfl⟩)
    · exact ⟨C ⟨a, ha⟩, polyChartHom_C V R₀ ⟨a, ha⟩⟩
    · exact ⟨X v, polyChartHom_X V R₀ v⟩

theorem polyChart_clear (h : ∀ x : F₀, ∃ a ∈ R₀, ∃ b ∈ R₀, b ≠ 0 ∧ x * b = a)
    (p : MvPolynomial V F₀) :
    ∃ b : R₀, (b : F₀) ≠ 0 ∧ ∃ q : MvPolynomial V R₀,
      p * C (b : F₀) = MvPolynomial.map (R₀.val : R₀ →+* F₀) q := by
  induction p using MvPolynomial.induction_on with
  | C x =>
    obtain ⟨a, ha, b, hb, hb0, e⟩ := h x
    refine ⟨⟨b, hb⟩, hb0, C ⟨a, ha⟩, ?_⟩
    rw [MvPolynomial.map_C, ← map_mul]
    exact congrArg C e
  | add p q hp hq =>
    obtain ⟨b, hb, p', e⟩ := hp
    obtain ⟨c, hc, q', f⟩ := hq
    refine ⟨b * c, mul_ne_zero hb hc, p' * C c + q' * C b, ?_⟩
    rw [map_add, map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_C, ← e, ← f]
    change (p + q) * C ((b : F₀) * c) = p * C (b : F₀) * C (c : F₀) + q * C (c : F₀) * C (b : F₀)
    rw [map_mul]
    ring
  | mul_X p v hp =>
    obtain ⟨b, hb, p', e⟩ := hp
    refine ⟨b, hb, p' * X v, ?_⟩
    rw [map_mul, MvPolynomial.map_X, ← e]
    ring

end PolyChart

theorem polyChart_smooth_fraction_lift : ∀ (K F₀ V : Type) [Field K] [Field F₀] [Algebra K F₀] [Finite V] (R₀ : Subalgebra K F₀) (R : Subalgebra K (FractionRing (MvPolynomial V F₀))), R = Algebra.adjoin K ((algebraMap F₀ (FractionRing (MvPolynomial V F₀))) '' (R₀ : Set F₀) ∪ Set.range fun v : V => algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) (MvPolynomial.X v)) → (Algebra.Smooth K R₀ → Algebra.Smooth K R) ∧ ((∀ x : F₀, ∃ a ∈ R₀, ∃ b ∈ R₀, b ≠ 0 ∧ x * b = a) → ∀ x : FractionRing (MvPolynomial V F₀), ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a) ∧ ∀ (S : Type) [CommRing S] [Algebra K S] (ψ : R₀ →ₐ[K] S) (t : V → S), ∃! ψ' : R →ₐ[K] S, (∀ (a : R₀) (h : algebraMap F₀ (FractionRing (MvPolynomial V F₀)) a ∈ R), ψ' ⟨_, h⟩ = ψ a) ∧ ∀ (v : V) (h : algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) (MvPolynomial.X v) ∈ R), ψ' ⟨_, h⟩ = t v := by
  intro K F₀ V _ _ _ _ R₀ R hR
  rw [← polyChartHom_range] at hR
  subst hR
  let e : MvPolynomial V R₀ ≃ₐ[K] (polyChartHom V R₀).range :=
    AlgEquiv.ofInjective _ (polyChartHom_injective V R₀)
  have he : ∀ p, ((e p : (polyChartHom V R₀).range) : FractionRing (MvPolynomial V F₀))
      = polyChartHom V R₀ p := fun p => rfl
  have heC : ∀ (a : R₀) (h : algebraMap F₀ (FractionRing (MvPolynomial V F₀)) a ∈
      (polyChartHom V R₀).range), (⟨_, h⟩ : (polyChartHom V R₀).range) = e (C a) :=
    fun a h => Subtype.ext (polyChartHom_C V R₀ a).symm
  have heX : ∀ (v : V) (h : algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀))
      (X v) ∈ (polyChartHom V R₀).range), (⟨_, h⟩ : (polyChartHom V R₀).range) = e (X v) :=
    fun v h => Subtype.ext (polyChartHom_X V R₀ v).symm
  refine ⟨fun hs => ?_, fun h x => ?_, fun S _ _ ψ t => ?_⟩
  · have : Algebra.Smooth R₀ (MvPolynomial V R₀) := ⟨inferInstance, inferInstance⟩
    have : Algebra.Smooth K (MvPolynomial V R₀) := Algebra.Smooth.comp K R₀ _
    exact Algebra.Smooth.of_equiv e
  · obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial V F₀) x
    obtain ⟨b, hb, p', e1⟩ := polyChart_clear V R₀ h p
    obtain ⟨c, hc, q', e2⟩ := polyChart_clear V R₀ h q
    have hq0 : algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) q ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
    have hne : ∀ d : F₀, d ≠ 0 →
        algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) (C d) ≠ 0 := by
      intro d hd h0
      rw [IsFractionRing.to_map_eq_zero_iff, MvPolynomial.C_eq_zero] at h0
      exact hd h0
    have h1 : polyChartHom V R₀ (p' * C c) =
        algebraMap (MvPolynomial V F₀) _ (p * C (b : F₀) * C (c : F₀)) := by
      rw [polyChartHom_apply, map_mul, MvPolynomial.map_C, e1]; rfl
    have h2 : polyChartHom V R₀ (q' * C b) =
        algebraMap (MvPolynomial V F₀) _ (q * C (c : F₀) * C (b : F₀)) := by
      rw [polyChartHom_apply, map_mul, MvPolynomial.map_C, e2]; rfl
    refine ⟨_, ⟨_, h1⟩, _, ⟨_, h2⟩, ?_, ?_⟩
    · rw [map_mul, map_mul]
      exact mul_ne_zero (mul_ne_zero hq0 (hne _ hc)) (hne _ hb)
    · simp only [map_mul]
      field_simp
  · let φ : MvPolynomial V R₀ →ₐ[K] S := MvPolynomial.aevalTower ψ t
    refine ⟨φ.comp e.symm.toAlgHom, ⟨fun a h => ?_, fun v h => ?_⟩, ?_⟩
    · rw [heC]
      simp [φ]
    · rw [heX]
      simp [φ]
    · rintro χ ⟨hC, hX⟩
      have : χ.comp e.toAlgHom = φ := by
        apply MvPolynomial.algHom_ext'
        · ext a
          have hm : algebraMap F₀ (FractionRing (MvPolynomial V F₀)) a ∈
            (polyChartHom V R₀).range := ⟨C a, polyChartHom_C V R₀ a⟩
          have := (congrArg χ (heC a hm)).symm.trans (hC a hm)
          simpa [φ] using this
        · intro v
          have hm : algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀))
            (X v) ∈ (polyChartHom V R₀).range := ⟨X v, polyChartHom_X V R₀ v⟩
          have := (congrArg χ (heX v hm)).symm.trans (hX v hm)
          simpa [φ] using this
      rw [← this]
      ext x
      simp

end GlobalTheory
