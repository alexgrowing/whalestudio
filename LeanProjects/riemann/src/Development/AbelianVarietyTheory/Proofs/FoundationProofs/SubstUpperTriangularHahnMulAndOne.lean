import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed

noncomputable section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion

namespace GlobalTheory.CyclotomicQExpansion

section Character

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ)

theorem exp_mem_range_of_isAlgClosed (x : ℚ) :
    Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ Set.range ε := by
  have hMΩ : ((x.den : ℕ) : Ω) ≠ 0 := by
    intro h
    have := congrArg ε h
    simp only [map_natCast, map_zero, Nat.cast_eq_zero] at this
    exact x.den_nz this
  haveI : NeZero ((x.den : ℕ) : Ω) := ⟨hMΩ⟩
  haveI : NeZero x.den := ⟨x.den_nz⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω x.den
  have hζ' := hζ.map_of_injective ε.injective
  have hw : Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul]
    have hx : (x : ℂ) * (x.den : ℂ) = (x.num : ℂ) := by exact_mod_cast Rat.mul_den_eq_num x
    have : (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = (x.num : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [← hx]; ring
    rw [this]; exact Complex.exp_int_mul_two_pi_mul_I _
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hw
  exact ⟨ζ ^ i, by rw [map_pow]; exact hi⟩

theorem eOm_spec (x : ℚ) : ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) :=
  Function.invFun_eq (exp_mem_range_of_isAlgClosed ε x)

theorem eOm_add (x y : ℚ) : eOm ε (x + y) = eOm ε x * eOm ε y := by
  apply ε.injective
  rw [map_mul, eOm_spec, eOm_spec, eOm_spec, ← Complex.exp_add]
  congr 1; push_cast; ring

theorem eOm_zero : eOm ε 0 = 1 := by
  apply ε.injective
  rw [eOm_spec, map_one]; simp

end Character

section Coeff

variable {R : Type*} [CommRing R]

theorem cm_coeff (c : ℚ → R) (φ : HahnSeries ℚ R) (r : ℚ) : (cm c φ).coeff r = c r * φ.coeff r := rfl

theorem cm_mul (c : ℚ → R) (hc : ∀ r s, c (r + s) = c r * c s) (φ ψ : HahnSeries ℚ R) :
    cm c (φ * ψ) = cm c φ * cm c ψ := by
  ext r
  have h1 : (cm c φ).support ⊆ φ.support := fun t ht h => ht (by simp [cm_coeff, h])
  have h2 : (cm c ψ).support ⊆ ψ.support := fun t ht h => ht (by simp [cm_coeff, h])
  rw [cm_coeff, HahnSeries.coeff_mul, HahnSeries.coeff_mul, Finset.mul_sum]
  have e1 : ∀ ij ∈ Finset.antidiagonal φ.isPWO_support ψ.isPWO_support r,
      c r * (φ.coeff ij.1 * ψ.coeff ij.2) = (cm c φ).coeff ij.1 * (cm c ψ).coeff ij.2 := by
    intro ij hij
    rw [Finset.mem_antidiagonal] at hij
    rw [cm_coeff, cm_coeff, ← hij.2.2, hc]; ring
  rw [Finset.sum_congr rfl e1]
  symm
  apply Finset.sum_subset
  · intro ij hij
    rw [Finset.mem_antidiagonal] at hij ⊢
    exact ⟨h1 hij.1, h2 hij.2.1, hij.2.2⟩
  · intro ij hij hn
    rw [Finset.mem_antidiagonal] at hij hn
    by_contra hne
    exact hn ⟨(HahnSeries.mem_support _ _).2 (ne_zero_and_ne_zero_of_mul hne).1,
      (HahnSeries.mem_support _ _).2 (ne_zero_and_ne_zero_of_mul hne).2, hij.2.2⟩

theorem cm_one (c : ℚ → R) (hc : c 0 = 1) : cm c (1 : HahnSeries ℚ R) = 1 := by
  ext r
  rw [cm_coeff, HahnSeries.coeff_one]
  split_ifs with h
  · subst h; rw [hc, mul_one]
  · rw [mul_zero]

theorem scale_mul {a : ℚ} (ha : 0 < a) (φ ψ : HahnSeries ℚ R) : scale a (φ * ψ) = scale a φ * scale a ψ := by
  simp only [scale, dif_pos ha]
  exact HahnSeries.embDomain_mul _ (fun x y => by simp [mul_add]) φ ψ

theorem scale_one {a : ℚ} (ha : 0 < a) : scale a (1 : HahnSeries ℚ R) = 1 := by
  simp only [scale, dif_pos ha]
  exact HahnSeries.embDomain_one _ (by simp)

end Coeff

theorem sub_mul_and_one : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (a b d : ℚ), 0 < a / d →
    ∀ φ ψ : HahnSeries ℚ Ω,
  sub ε a b d (φ * ψ) = sub ε a b d φ * sub ε a b d ψ ∧ sub ε a b d 1 = 1 := by
  intro Ω _ _ _ ε a b d h φ ψ
  have hc : ∀ r s : ℚ, eOm ε ((r + s) * b / d) = eOm ε (r * b / d) * eOm ε (s * b / d) := by
    intro r s; rw [← eOm_add]; congr 1; ring
  have h0 : eOm ε (0 * b / d) = 1 := by rw [zero_mul, zero_div, eOm_zero]
  refine ⟨?_, ?_⟩
  · simp only [sub]; rw [cm_mul _ hc, scale_mul h]
  · simp only [sub]; rw [cm_one _ h0, scale_one h]

end GlobalTheory.CyclotomicQExpansion
