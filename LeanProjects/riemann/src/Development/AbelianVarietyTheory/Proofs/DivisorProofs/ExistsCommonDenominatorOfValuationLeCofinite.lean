import Mathlib
open NumberField IsDedekindDomain

namespace GlobalTheory.ValBoundDenom

theorem exists_nat_le_exp (a : WithZero (Multiplicative ℤ)) : ∃ n : ℕ, a ≤ WithZero.exp (n : ℤ) := by
  induction a using WithZero.recZeroCoe with
  | zero => exact ⟨0, zero_le'⟩
  | coe m =>
    refine ⟨(Multiplicative.toAdd m).toNat, ?_⟩
    show (m : WithZero (Multiplicative ℤ)) ≤ ((Multiplicative.ofAdd ((Multiplicative.toAdd m).toNat : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    rw [WithZero.coe_le_coe]
    exact Int.self_le_toNat (Multiplicative.toAdd m)

theorem exists_common_denominator_of_valuation_le (E : Type) [Field E] [NumberField E]
    (β : IsDedekindDomain.HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ))
    (hβ : ∀ᶠ w in Filter.cofinite, β w ≤ 1) : ∃ D : 𝓞 E, D ≠ 0 ∧
      ∀ x : E, (∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 E), w.valuation E x ≤ β w) →
        IsIntegral ℤ ((D : E) * x) := by
  classical
  have hfin : {w | ¬ β w ≤ 1}.Finite := Filter.eventually_cofinite.mp hβ
  set T := hfin.toFinset with hT
  choose k hk using fun w => exists_nat_le_exp (β w)
  set I : Ideal (𝓞 E) := ∏ w ∈ T, w.asIdeal ^ k w with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, ← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    intro w _
    exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact w.ne_bot)
  obtain ⟨D, hDI, hD0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
  refine ⟨D, hD0, fun x hx => ?_⟩
  have hle : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 E), w.valuation E ((D : E) * x) ≤ 1 := by
    intro w
    rw [map_mul]
    by_cases hw : w ∈ T
    · have hmem : D ∈ w.asIdeal ^ k w :=
        (Finset.inf_le hw : T.inf (fun w => w.asIdeal ^ k w) ≤ _) (Ideal.prod_le_inf hDI)
      have h1 : w.valuation E (D : E) ≤ WithZero.exp (-(k w : ℤ)) := by
        rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        exact (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem _ _ _).mpr hmem
      have h2 : w.valuation E x ≤ WithZero.exp (k w : ℤ) := (hx w).trans (hk w)
      calc w.valuation E (D : E) * w.valuation E x
          ≤ WithZero.exp (-(k w : ℤ)) * WithZero.exp (k w : ℤ) := mul_le_mul' h1 h2
        _ = 1 := by rw [← WithZero.exp_add]; simp
    · have hw1 : β w ≤ 1 := by
        by_contra h
        exact hw (by rw [hT, Set.Finite.mem_toFinset]; exact h)
      exact mul_le_one' (IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _) ((hx w).trans hw1)
  obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one E _ hle
  rw [← hr]
  exact r.isIntegral_coe

end GlobalTheory.ValBoundDenom
