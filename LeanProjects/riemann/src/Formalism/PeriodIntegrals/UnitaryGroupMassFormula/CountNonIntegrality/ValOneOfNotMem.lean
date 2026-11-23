import Mathlib

noncomputable section

namespace PI.CntNotIntW

open NumberField IsDedekindDomain ValuativeRel

section Val

variable {E : Type} [Field E] [NumberField E] {K : Type} [Field K] [ValuativeRel K]

theorem sig_int (σ : E →+* K) (o : 𝓞 E) : σ (o : E) ∈ 𝒪[K] :=
  (Valuation.integer.integers (valuation K)).mem_of_integral
    ((map_isIntegral_int σ (RingOfIntegers.isIntegral_coe o)).tower_top)

theorem sig_le_one (σ : E →+* K) (o : 𝓞 E) : valuation K (σ (o : E)) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).1 (sig_int σ o)

def vIdeal (σ : E →+* K) : Ideal (𝓞 E) where
  carrier := {o | valuation K (σ (o : E)) < 1}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq, AddMemClass.coe_add, map_add] at hx hy ⊢
    exact Valuation.map_add_lt _ hx hy
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, ZeroMemClass.coe_zero, map_zero, Valuation.map_zero]
    exact zero_lt_one
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq, smul_eq_mul, MulMemClass.coe_mul, map_mul, Valuation.map_mul] at hx ⊢
    exact mul_lt_of_le_one_of_lt (sig_le_one σ c) hx

theorem mem_vIdeal (σ : E →+* K) (o : 𝓞 E) : o ∈ vIdeal σ ↔ valuation K (σ (o : E)) < 1 := Iff.rfl

theorem vIdeal_prime (σ : E →+* K) : (vIdeal σ).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_vIdeal]
    simp
  · intro x y hxy
    rw [mem_vIdeal, mem_vIdeal]
    rw [mem_vIdeal] at hxy
    by_contra hc
    push Not at hc
    have hx : valuation K (σ (x : E)) = 1 := le_antisymm (sig_le_one σ x) hc.1
    have hy : valuation K (σ (y : E)) = 1 := le_antisymm (sig_le_one σ y) hc.2
    simp only [MulMemClass.coe_mul, map_mul, Valuation.map_mul, hx, hy, mul_one] at hxy
    exact lt_irrefl _ hxy

def vPrime (σ : E →+* K) (l : ℕ) (hl0 : l ≠ 0) (hl : valuation K (l : K) < 1) : HeightOneSpectrum (𝓞 E) where
  asIdeal := vIdeal σ
  isPrime := vIdeal_prime σ
  ne_bot := by
    intro h
    have hm : ((l : ℕ) : 𝓞 E) ∈ vIdeal σ := by
      rw [mem_vIdeal]
      simpa using hl
    rw [h, Ideal.mem_bot] at hm
    exact hl0 (by exact_mod_cast hm)

theorem val_one_of_not_mem (σ : E →+* K) (l : ℕ) (hl0 : l ≠ 0) (hl : valuation K (l : K) < 1) (s : 𝓞 E)
    (hs : s ∉ (vPrime σ l hl0 hl).asIdeal) : valuation K (σ (s : E)) = 1 :=
  le_antisymm (sig_le_one σ s) (not_lt.1 hs)

theorem div_q (σ : E →+* K) (q m : 𝒪[K]) (j n : ℕ) (c x : E) (o : 𝓞 E)
    (hc : valuation K (σ c) = 1) (hn : (n : K) = (q : K) ^ j * m) (h : c * x = (n : E) * o) :
    ∃ t : 𝒪[K], σ x = (q : K) ^ j * t := by
  have hc0 : σ c ≠ 0 := by
    intro h0
    rw [h0, Valuation.map_zero] at hc
    exact zero_ne_one hc
  have hσ : σ c * σ x = (n : K) * σ (o : E) := by
    have := congrArg σ h
    simpa [map_mul, map_natCast] using this
  have hm : valuation K (m : K) ≤ 1 := (Valuation.mem_integer_iff _ _).1 m.2
  have ho : valuation K (σ (o : E)) ≤ 1 := sig_le_one σ o
  refine ⟨⟨(m : K) * σ (o : E) * (σ c)⁻¹, ?_⟩, ?_⟩
  · rw [Valuation.mem_integer_iff, Valuation.map_mul, Valuation.map_mul, Valuation.map_inv, hc, inv_one, mul_one]
    exact mul_le_one' hm ho
  · simp only
    rw [hn] at hσ
    field_simp
    linear_combination hσ

end Val

end PI.CntNotIntW
