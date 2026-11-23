import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.Kloc

noncomputable section

namespace ReciprocityTheory.Neutral.Cmp

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
open scoped Pointwise

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]

theorem Compat.valuation_le_one_iff {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) (x : Ω) :
    A.valuation x ≤ 1 ↔ ‖ι x‖ ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff]
  exact h x

theorem Compat.valuation_lt_one_iff {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) (x : Ω) :
    A.valuation x < 1 ↔ ‖ι x‖ < 1 := by
  by_cases hx : x = 0
  · subst hx
    simp
  · have hx' : x⁻¹ ≠ 0 := inv_ne_zero hx
    have h1 : A.valuation x < 1 ↔ 1 < A.valuation x⁻¹ := by
      rw [Valuation.one_lt_val_iff _ hx', inv_inv]
    have hn : 0 < ‖ι x‖ := norm_pos_iff.mpr ((map_ne_zero ι).mpr hx)
    rw [h1, ← not_le, h.valuation_le_one_iff, map_inv₀, norm_inv, not_le, one_lt_inv₀ hn]

theorem valuation_intCast_lt_one_iff [CharZero Ω] (B : ValuationSubring Ω) (hp : B.valuation (p : Ω) < 1) (n : ℤ) :
    B.valuation (n : Ω) < 1 ↔ (p : ℤ) ∣ n := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hle : ∀ m : ℤ, B.valuation (m : Ω) ≤ 1 := fun m =>
    (B.valuation_le_one_iff _).mpr (intCast_mem B m)
  constructor
  · intro hn
    by_contra hpn
    obtain ⟨a, b, hab⟩ := (Prime.coprime_iff_not_dvd hpZ).mpr hpn
    have h1 : B.valuation ((a : Ω) * (p : Ω)) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle a)) hp
    have h2 : B.valuation ((b : Ω) * (n : Ω)) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle b)) hn
    have h3 : ((a : Ω) * (p : Ω)) + (b : Ω) * (n : Ω) = 1 := by exact_mod_cast hab
    have h4 := B.valuation.map_add ((a : Ω) * (p : Ω)) ((b : Ω) * (n : Ω))
    rw [h3, map_one] at h4
    exact absurd (lt_of_le_of_lt h4 (max_lt h1 h2)) (lt_irrefl 1)
  · rintro ⟨m, rfl⟩
    push_cast
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hle m)) hp

def ratPrime (p : ℕ) [Fact p.Prime] : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.comap (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) (Ideal.span {(p : ℤ)})
  isPrime := by
    have : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp Fact.out)
    exact Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    have hmem : ((p : ℕ) : 𝓞 ℚ) ∈ Ideal.comap (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) (Ideal.span {(p : ℤ)}) := by
      rw [Ideal.mem_comap, map_natCast, Ideal.mem_span_singleton]
    rw [h, Ideal.mem_bot] at hmem
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hmem)

theorem lies_over_ratPrime [CharZero Ω] (B : ValuationSubring Ω) (hp : B.valuation (p : Ω) < 1) (x : 𝓞 ℚ) :
    B.valuation (algebraMap ℚ Ω (x : ℚ)) < 1 ↔ x ∈ (ratPrime p).asIdeal := by
  have hx : (x : ℚ) = ((Rat.ringOfIntegersEquiv x : ℤ) : ℚ) := by
    conv_lhs => rw [← Rat.ringOfIntegersEquiv.symm_apply_apply x]
    simp
  rw [hx, map_intCast, valuation_intCast_lt_one_iff B hp]
  show _ ↔ Rat.ringOfIntegersEquiv x ∈ Ideal.span {(p : ℤ)}
  rw [Ideal.mem_span_singleton]

theorem mem_comap_ball (ι : Ω →+* PadicAlgCl p) (x : Ω) :
    x ∈ ((PadicAlgCl.valued p).v.valuationSubring.comap ι) ↔ ‖ι x‖ ≤ 1 := by
  rw [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff]
  show ‖ι x‖₊ ≤ 1 ↔ ‖ι x‖ ≤ 1
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]

variable (F) in
include F in

theorem exists_compat (A : ValuationSubring Ω) (hp : A.valuation (p : Ω) < 1) :
    ∃ ι : Ω →+* PadicAlgCl p, Compat p A ι := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  have : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed F, inferInstance⟩
  let ι0 : Ω →+* PadicAlgCl p := (IsAlgClosed.lift (R := ℚ) (S := Ω) (M := PadicAlgCl p) : Ω →ₐ[ℚ] PadicAlgCl p)
  let A0 : ValuationSubring Ω := (PadicAlgCl.valued p).v.valuationSubring.comap ι0
  have h0 : Compat p A0 ι0 := mem_comap_ball ι0
  have hp0 : A0.valuation (p : Ω) < 1 := by
    rw [h0.valuation_lt_one_iff, map_natCast]
    have : ((Valued.v (p : PadicAlgCl p) : NNReal) : ℝ) = ‖(p : PadicAlgCl p)‖ := PadicAlgCl.valuation_coe p _
    rw [← this, PadicAlgCl.valuation_p]
    push_cast
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    exact (div_lt_one (by linarith)).mpr hp1
  obtain ⟨g, hg⟩ := exists_smul_eq_of_over (F := ℚ) (lies_over_ratPrime A0 hp0) (lies_over_ratPrime A hp)
  refine ⟨ι0.comp ((g⁻¹ : Ω ≃ₐ[ℚ] Ω) : Ω →+* Ω), fun x => ?_⟩
  rw [← hg]
  have := ValuationSubring.smul_mem_pointwise_smul_iff (g := g) (S := A0) (x := g⁻¹ • x)
  rw [smul_inv_smul] at this
  rw [this, h0]
  rfl

end ReciprocityTheory.Neutral.Cmp
