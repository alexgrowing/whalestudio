import Mathlib

namespace GlobalTheory.IntegralNormSmallIdeal

open NumberField

theorem norm_le_one_of_isIntegral {l : ℕ} [Fact (Nat.Prime l)] (y : PadicAlgCl l)
    (hy : IsIntegral ℤ y) : ‖y‖ ≤ 1 := by
  have hv := Valuation.integer.integers (Valued.v : Valuation (PadicAlgCl l) NNReal)
  have h2 : IsIntegral (Valued.v : Valuation (PadicAlgCl l) NNReal).integer y :=
    IsIntegral.tower_top hy
  have h3 := hv.isIntegral_iff_v_le_one.mp h2
  rw [PadicAlgCl.valuation_def] at h3
  exact_mod_cast h3

theorem norm_natCast_prime {l : ℕ} [Fact (Nat.Prime l)] :
    ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
  have h0 := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [map_natCast] at h0
  rw [h0]
  exact Padic.norm_p_lt_one

theorem norm_map_le_one {l : ℕ} [Fact (Nat.Prime l)] {E : Type} [Field E]
    (c : E →+* PadicAlgCl l) (x : 𝓞 E) : ‖c (x : E)‖ ≤ 1 := by
  apply norm_le_one_of_isIntegral
  have h0 := (NumberField.RingOfIntegers.isIntegral_coe x).map c.toIntAlgHom
  simpa using h0

def smallIdeal {l : ℕ} [Fact (Nat.Prime l)] {E : Type} [Field E]
    (c : E →+* PadicAlgCl l) : Ideal (𝓞 E) where
  carrier := {x | ‖c (x : E)‖ < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    have : ((a + b : 𝓞 E) : E) = (a : E) + (b : E) := map_add (algebraMap (𝓞 E) E) a b
    rw [this, map_add]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    have : ((0 : 𝓞 E) : E) = 0 := map_zero (algebraMap (𝓞 E) E)
    rw [this, map_zero, norm_zero]
    exact zero_lt_one
  smul_mem' := by
    intro r x hx
    simp only [Set.mem_ofPred_eq, smul_eq_mul] at hx ⊢
    have : ((r * x : 𝓞 E) : E) = (r : E) * (x : E) := map_mul (algebraMap (𝓞 E) E) r x
    rw [this, map_mul, norm_mul]
    calc ‖c (r : E)‖ * ‖c (x : E)‖ ≤ 1 * ‖c (x : E)‖ :=
          mul_le_mul_of_nonneg_right (norm_map_le_one c r) (norm_nonneg _)
      _ < 1 := by rwa [one_mul]

theorem mem_smallIdeal {l : ℕ} [Fact (Nat.Prime l)] {E : Type} [Field E]
    (c : E →+* PadicAlgCl l) (x : 𝓞 E) : x ∈ smallIdeal c ↔ ‖c (x : E)‖ < 1 := Iff.rfl

theorem smallIdeal_isPrime {l : ℕ} [Fact (Nat.Prime l)] {E : Type} [Field E]
    (c : E →+* PadicAlgCl l) : (smallIdeal c).IsPrime := by
  refine Ideal.isPrime_iff.2 ⟨?_, fun {x y} hxy => ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_smallIdeal]
    simp
  · rw [mem_smallIdeal, mem_smallIdeal]
    rw [mem_smallIdeal] at hxy
    by_contra hcon
    push_neg at hcon
    have h1 := norm_map_le_one c x
    have h2 := norm_map_le_one c y
    have e : ((x * y : 𝓞 E) : E) = (x : E) * (y : E) := map_mul (algebraMap (𝓞 E) E) x y
    rw [e, map_mul, norm_mul] at hxy
    nlinarith [hcon.1, hcon.2]

theorem natCast_mem_smallIdeal {l : ℕ} [Fact (Nat.Prime l)] {E : Type} [Field E]
    (c : E →+* PadicAlgCl l) : ((l : ℕ) : 𝓞 E) ∈ smallIdeal c := by
  rw [mem_smallIdeal]
  have e : (((l : ℕ) : 𝓞 E) : E) = ((l : ℕ) : E) := map_natCast (algebraMap (𝓞 E) E) l
  rw [e, map_natCast]
  exact norm_natCast_prime

theorem exists_place_of_embedding {l : ℕ} [inst : Fact (Nat.Prime l)] {E : Type} [inst_1 : Field E]
    [NumberField E] (c : E →+* PadicAlgCl l) :
    ∃ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)),
      (↑l : NumberField.RingOfIntegers E) ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v ∧
      ∀ (x : NumberField.RingOfIntegers E), x ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v ↔
        ‖(c : E → PadicAlgCl l) (↑x : E)‖ < (1 : ℝ) := by
  have hl0 : ((l : ℕ) : NumberField.RingOfIntegers E) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  refine ⟨⟨smallIdeal c, smallIdeal_isPrime c, fun h => hl0 ?_⟩, natCast_mem_smallIdeal c, fun x => mem_smallIdeal c x⟩
  have h0 := natCast_mem_smallIdeal (E := E) c
  rw [h] at h0
  exact (Submodule.mem_bot _).1 h0

end GlobalTheory.IntegralNormSmallIdeal
