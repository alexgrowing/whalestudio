import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau

noncomputable section

open GlobalTheory.LatVal (Sz)

namespace GlobalTheory.QFam

theorem exists_algebraic_norm_eq_rpow (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (q : ℚ) :
    ∃ x : algebraicClosure ℚ ℂ, x ≠ 0 ∧ ‖lam x‖ = (l : ℝ) ^ (-(q : ℝ)) := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hlc : (l : algebraicClosure ℚ ℂ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
    have h1 := PadicComplex.norm_extends' l (l : ℚ_[l])
    rw [Padic.norm_p] at h1
    simpa using h1
  haveI : IsAlgClosed (algebraicClosure ℚ ℂ) := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq ((l : algebraicClosure ℚ ℂ) ^ q.num) q.den_pos
  refine ⟨x, ?_, ?_⟩
  · rintro rfl
    rw [zero_pow q.den_ne_zero] at hx
    exact zpow_ne_zero _ hlc hx.symm
  · have h1 : ‖lam x‖ ^ q.den = ((l : ℝ) ^ (-(q : ℝ))) ^ q.den := by
      rw [← norm_pow, ← map_pow, hx, map_zpow₀, map_natCast, norm_zpow, hl, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le,
        inv_zpow', ← Real.rpow_intCast]
      congr 1
      have h2 : (q : ℝ) * (q.den : ℝ) = (q.num : ℝ) := by exact_mod_cast q.mul_den_eq_num
      push_cast
      rw [neg_mul, h2]
    exact (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg hl0.le _) q.den_ne_zero).1 h1

theorem sz_of_norm_eq {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} {r : ℝ} {x : algebraicClosure ℚ ℂ}
    (hx : ‖lam x‖ = (l : ℝ) ^ (-r)) : Sz l lam (-r) (x : ℂ) :=
  ⟨x.2, hx.le⟩

theorem sz_inv_of_norm_eq {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} {r : ℝ} {x : algebraicClosure ℚ ℂ}
    (hx : ‖lam x‖ = (l : ℝ) ^ (-r)) : Sz l lam r (x : ℂ)⁻¹ := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  refine ⟨inv_mem x.2, ?_⟩
  have e : (⟨(x : ℂ)⁻¹, inv_mem x.2⟩ : algebraicClosure ℚ ℂ) = x⁻¹ := rfl
  rw [e, map_inv₀, norm_inv, hx, Real.rpow_neg hl0.le, inv_inv]

theorem exists_sz_scale : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∀ q : ℚ,
    ∃ c : ℂ, c ≠ 0 ∧ Sz l lam (-(q : ℝ)) c ∧ Sz l lam q c⁻¹ := by
  intro l _ lam q
  obtain ⟨x, hx0, hx⟩ := exists_algebraic_norm_eq_rpow l lam q
  exact ⟨x, fun h => hx0 (Subtype.ext h), sz_of_norm_eq hx, sz_inv_of_norm_eq hx⟩

end GlobalTheory.QFam
