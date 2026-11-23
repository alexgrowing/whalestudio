import Mathlib

open Polynomial IsLocalRing

namespace GlobalTheory

theorem kummer_residue_aeval (T V : Type) [CommRing T] [IsLocalRing T] [CommRing V] [IsLocalRing V]
    [Algebra T V] [IsLocalHom (algebraMap T V)] (γ : V) (p : T[X]) :
    residue V (aeval γ p) = aeval (residue V γ) (p.map (residue T)) := by
  induction p using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | monomial n a hp => simp [hp, pow_succ, ← mul_assoc]

theorem kummer_step_one (T V : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra T V]
    [IsLocalHom (algebraMap T V)]
    (γ : V) (ϖ u : T) (k : ℕ) (hϖ : Irreducible ϖ) (hu : IsUnit u) (hk : IsUnit (k : T))
    (hk0 : 0 < k) (hγ : γ ^ k = algebraMap T V u) (h : T[X])
    (hm : aeval γ h ∈ maximalIdeal V) :
    ∃ ν r : T[X], IsUnit (aeval γ ν) ∧
      aeval γ h * aeval γ ν = algebraMap T V ϖ * aeval γ r := by
  set γ' := residue V γ with hγ'
  set f : (ResidueField T)[X] := X ^ k - C (residue T u) with hf
  have hkκ : ((k : ℕ) : ResidueField T) ≠ 0 := by
    have := (hk.map (residue T)).ne_zero
    simpa using this
  have hu' : residue T u ≠ 0 := (hu.map (residue T)).ne_zero
  have hsep : f.Separable := separable_X_pow_sub_C _ hkκ hu'
  have hfγ : aeval γ' f = 0 := by
    have := congrArg (residue V) hγ
    simp only [map_pow] at this
    simp [hf, hγ', this]
  have hhm : aeval γ' (h.map (residue T)) = 0 := by
    rw [hγ', ← kummer_residue_aeval]
    exact (residue_eq_zero_iff _).mpr hm
  obtain ⟨νb, hνb⟩ := minpoly.dvd (ResidueField T) γ' hfγ
  obtain ⟨qb, hqb⟩ := minpoly.dvd (ResidueField T) γ' hhm
  have hνne : aeval γ' νb ≠ 0 := by
    intro h0
    have hcop : IsCoprime (minpoly (ResidueField T) γ') νb := Separable.isCoprime (hνb ▸ hsep)
    obtain ⟨a, b, hab⟩ := hcop
    have := congrArg (aeval γ') hab
    simp [minpoly.aeval, h0] at this
  obtain ⟨ν, rfl⟩ := map_surjective (residue T) residue_surjective νb
  obtain ⟨q, rfl⟩ := map_surjective (residue T) residue_surjective qb
  set D : T[X] := h * ν - q * (X ^ k - C u) with hD
  have hDm : D.map (residue T) = 0 := by
    have e1 : (X ^ k - C u).map (residue T) = f := by simp [hf]
    rw [hD, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul, e1, hνb, hqb]
    ring
  have hDI : D ∈ Ideal.span {C ϖ} := by
    have : D ∈ Ideal.map (C : T →+* T[X]) (maximalIdeal T) := by
      rw [Ideal.mem_map_C_iff]
      intro n
      rw [← residue_eq_zero_iff, ← coeff_map, hDm, coeff_zero]
    rwa [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton] at this
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hDI
  refine ⟨ν, r, ?_, ?_⟩
  · rw [← residue_ne_zero_iff_isUnit, kummer_residue_aeval]
    exact hνne
  · have := congrArg (aeval γ) hr
    simp only [hD, map_mul, map_sub, map_pow, aeval_X, aeval_C, hγ, sub_self, mul_zero,
      sub_zero] at this
    rw [← this, mul_comm]

theorem kummer_valuation : ∀ (T V : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra T V] [IsLocalHom (algebraMap T V)],
    Function.Injective (algebraMap T V) →
    ∀ (γ : V) (ϖ u : T) (k : ℕ), Irreducible ϖ → IsUnit u → IsUnit (k : T) → 0 < k →
    γ ^ k = algebraMap T V u →
    ∀ h : Polynomial T, Polynomial.aeval γ h = 0 ∨
      ∃ (a : ℕ) (h' c : Polynomial T), IsUnit (Polynomial.aeval γ c) ∧ IsUnit (Polynomial.aeval γ h') ∧
        Polynomial.aeval γ c * Polynomial.aeval γ h = algebraMap T V ϖ ^ a * Polynomial.aeval γ h' := by
  intro T V _ _ _ _ _ _ _ _ hinj γ ϖ u k hϖ hu hk hk0 hγ h
  by_cases h0 : aeval γ h = 0
  · exact Or.inl h0
  right
  have hϖV : ¬ IsUnit (algebraMap T V ϖ) := fun h' => hϖ.not_isUnit (isUnit_of_map_unit _ _ h')
  suffices H : ∀ x : V, ∀ h : T[X], aeval γ h = x → x ≠ 0 →
      ∃ (a : ℕ) (h' c : T[X]), IsUnit (aeval γ c) ∧ IsUnit (aeval γ h') ∧
        aeval γ c * aeval γ h = algebraMap T V ϖ ^ a * aeval γ h' from H _ h rfl h0
  intro x
  refine (wellFounded_dvdNotUnit (α := V)).induction
    (C := fun x => ∀ h : T[X], aeval γ h = x → x ≠ 0 →
      ∃ (a : ℕ) (h' c : T[X]), IsUnit (aeval γ c) ∧ IsUnit (aeval γ h') ∧
        aeval γ c * aeval γ h = algebraMap T V ϖ ^ a * aeval γ h') x ?_
  intro x ih h hx hx0
  subst hx
  by_cases hunit : IsUnit (aeval γ h)
  · exact ⟨0, h, 1, by simp, hunit, by simp⟩
  have hm : aeval γ h ∈ maximalIdeal V := (mem_maximalIdeal _).mpr hunit
  obtain ⟨ν, r, hν, hr⟩ := kummer_step_one T V γ ϖ u k hϖ hu hk hk0 hγ h hm
  have hr0 : aeval γ r ≠ 0 := by
    intro h'
    rw [h', mul_zero] at hr
    exact mul_ne_zero hx0 hν.ne_zero hr
  have hdvd : DvdNotUnit (aeval γ r) (aeval γ h) := by
    refine ⟨hr0, algebraMap T V ϖ * ↑hν.unit⁻¹, ?_, ?_⟩
    · intro hu'
      exact hϖV (isUnit_of_mul_isUnit_left hu')
    · calc aeval γ h = aeval γ h * aeval γ ν * ↑hν.unit⁻¹ := by
            rw [mul_assoc, IsUnit.mul_val_inv, mul_one]
        _ = _ := by rw [hr]; ring
  obtain ⟨a, h', c, hc, hh', he⟩ := ih _ hdvd r rfl hr0
  refine ⟨a + 1, h', c * ν, ?_, hh', ?_⟩
  · rw [map_mul]
    exact hc.mul hν
  · calc aeval γ (c * ν) * aeval γ h = aeval γ c * (aeval γ h * aeval γ ν) := by
          rw [map_mul]; ring
      _ = algebraMap T V ϖ * (aeval γ c * aeval γ r) := by rw [hr]; ring
      _ = _ := by rw [he]; ring

end GlobalTheory
