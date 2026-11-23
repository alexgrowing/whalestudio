import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory.BasePointFree

theorem exists_ne_zero_pair (g : ℂ → ℂ) (hg : Differentiable ℂ g) (h1 : g 1 ≠ 0) (m : ℂ)
    (hm : m ≠ 0) : ∃ t : ℂ, g t ≠ 0 ∧ g (-(m * t)) ≠ 0 := by
  by_contra hne
  push Not at hne
  have hg' : Differentiable ℂ (fun t : ℂ => g (-(m * t))) := hg.comp (by fun_prop)
  have A : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  have B : AnalyticOnNhd ℂ (fun t : ℂ => g (-(m * t))) Set.univ := fun z _ => hg'.analyticAt z
  have := AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero A B (fun z _ => by
    by_cases h : g z = 0
    · simp [h]
    · simp [hne z h]) isPreconnected_univ
  rcases this with h | h
  · exact h1 (h 1 (Set.mem_univ _))
  · have := h (-m⁻¹) (Set.mem_univ _)
    apply h1
    simpa [hm] using this

theorem HC_add_smul_left {ι : Type} [Fintype ι] {n : ℕ} (w c γ : Fin n → EuclideanSpace ℂ ι)
    (a : ℂ) : HC (w + a • c) γ = HC w γ + a * HC c γ := by
  simp only [HC, Hf, Pi.add_apply, Pi.smul_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem prod_translate_mem {E : Type} [Field E] [NumberField E] (X : PT E) {n : ℕ}
    (s : (Fin n → Vsp X.dim) → ℂ) (hs : s ∈ X.Sec 1 n) (m : ℕ) (c : Fin n → Vsp X.dim) :
    (fun w => s (w + (1 : ℂ) • c) ^ m * s (w + (-(m : ℂ)) • c)) ∈ X.Sec (m + 1) n := by
  obtain ⟨hd, hs⟩ := hs
  refine ⟨?_, fun γ hγ v => ?_⟩
  · exact ((hd.comp (by fun_prop)).pow m).mul (hd.comp (by fun_prop))
  · simp only
    rw [add_right_comm v γ, add_right_comm v γ, hs γ hγ, hs γ hγ, HC_add_smul_left,
      HC_add_smul_left, mul_pow, mul_pow, ← Complex.exp_nat_mul]
    have : ((m + 1 : ℕ) : ℂ) * Real.pi * HC v γ + ((m + 1 : ℕ) : ℂ) * Real.pi * HC γ γ / 2 =
        (m : ℂ) * (((1 : ℕ) : ℂ) * Real.pi * (HC v γ + 1 * HC c γ) +
          ((1 : ℕ) : ℂ) * Real.pi * HC γ γ / 2) +
        (((1 : ℕ) : ℂ) * Real.pi * (HC v γ + -(m : ℂ) * HC c γ) +
          ((1 : ℕ) : ℂ) * Real.pi * HC γ γ / 2) := by
      push_cast; ring
    rw [this, Complex.exp_add ((m : ℂ) * _)]
    ring

theorem exists_sec_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (s : (Fin 1 → Vsp X.dim) → ℂ), s ∈ X.Sec 1 1 → s ≠ 0 → ∀ q : ℕ, 2 ≤ q → ∀ v : Fin 1 → Vsp X.dim, ∃ F ∈ X.Sec q 1, F v ≠ 0 := by
  intro E _ _ _ X s hs hs0 q hq v
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hs0
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  obtain ⟨t, h1, h2⟩ := exists_ne_zero_pair (fun t : ℂ => s (v + t • (p - v)))
    (hs.1.comp (by fun_prop)) (by simpa using hp) m hm
  refine ⟨_, prod_translate_mem X s hs m (t • (p - v)), ?_⟩
  refine mul_ne_zero (pow_ne_zero _ (by simpa using h1)) ?_
  rwa [smul_smul, neg_mul]

end GlobalTheory.BasePointFree
