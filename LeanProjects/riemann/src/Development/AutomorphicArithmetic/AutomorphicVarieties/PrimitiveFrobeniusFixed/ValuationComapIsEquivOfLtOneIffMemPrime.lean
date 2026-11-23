import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem int_le {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {b : Ω} (hb : IsIntegral ℤ b) :
    A.valuation b ≤ 1 := by
  have h : IsIntegral A b := hb.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [A.valuation_le_one_iff, ← hy]
  exact y.2

theorem UpperTheory.valuation_comap_isEquiv_of_lt_one_iff_mem_prime :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] (ι : K →+* Ω) (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 K)), (∀ y : 𝓞 K, A.valuation (ι (y : K)) < 1 ↔ y ∈ w.asIdeal) → (A.valuation.comap ι).IsEquiv (w.valuation K) := by
  intro K Ω _ _ _ ι A w h
  have hle : ∀ y : 𝓞 K, A.valuation (ι (y : K)) ≤ 1 := fun y =>
    int_le A (y.isIntegral_coe.map ι.toIntAlgHom)
  have key : ∀ x : K, w.valuation K x ≤ 1 → ∃ a s : 𝓞 K, s ∉ w.asIdeal ∧ x * (s : K) = (a : K) ∧
      A.valuation (ι x) = A.valuation (ι (a : K)) := by
    intro x hx
    obtain ⟨a, s, hs⟩ := w.exists_primeCompl_mul_eq_of_integer x hx
    have hs' : (s : 𝓞 K) ∉ w.asIdeal := s.2
    have hs2 : x * ((s : 𝓞 K) : K) = (a : K) := hs
    refine ⟨a, s, hs', hs2, ?_⟩
    have h1 : A.valuation (ι ((s : 𝓞 K) : K)) = 1 :=
      le_antisymm (hle _) (not_lt.1 fun hh => hs' ((h _).1 hh))
    rw [← hs2, map_mul, map_mul, h1, mul_one]
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  rw [Valuation.comap_apply]
  constructor
  · intro hx
    by_contra hw
    have hw' : 1 < w.valuation K x := not_le.1 hw
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hw'
    have hinv : w.valuation K x⁻¹ < 1 := by
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ hw'
    obtain ⟨a, s, -, hs2, he⟩ := key x⁻¹ hinv.le
    have ha : w.valuation K (a : K) < 1 := by
      rw [← hs2, map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hinv (w.valuation_le_one s)
    have ha' : a ∈ w.asIdeal := (w.valuation_lt_one_iff_mem a).1 ha
    have h2 : A.valuation (ι x⁻¹) < 1 := he ▸ (h a).2 ha'
    have h3 := mul_lt_one_of_nonneg_of_lt_one_left zero_le h2 hx
    rw [← map_mul, ← map_mul, inv_mul_cancel₀ hx0, map_one, map_one] at h3
    exact lt_irrefl _ h3
  · intro hx
    obtain ⟨a, s, -, -, he⟩ := key x hx
    rw [he]
    exact hle a
