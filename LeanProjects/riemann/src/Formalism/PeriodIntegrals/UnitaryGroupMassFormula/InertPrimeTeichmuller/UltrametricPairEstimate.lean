import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeTeichmuller.TeichNeZero

open NumberField Filter Topology

noncomputable section

namespace PI.OkpW

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [hp : Fact p.Prime]

def gens (p : ℕ) [Fact p.Prime] : Set (ℂ_[p] × ℂ_[p]) :=
  {x | ∃ ζ : ℂ_[p], ζ ^ (p ^ 2 - 1) = 1 ∧ x = (ζ, ζ ^ p)}

theorem pair_mem_of_pow (t : ℂ_[p]) (ht : t ^ (p ^ 2) = t) :
    (t, t ^ p) ∈ Subring.closure (gens p) := by
  by_cases h0 : t = 0
  · subst h0
    have e : ((0 : ℂ_[p]), (0 : ℂ_[p]) ^ p) = 0 := by
      simp [zero_pow hp.out.ne_zero]
    rw [e]
    exact zero_mem _
  · apply Subring.subset_closure
    refine ⟨t, ?_, rfl⟩
    have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.out.pos
    have e : t ^ (p ^ 2 - 1) * t = 1 * t := by
      rw [← pow_succ, Nat.sub_add_cancel h1, ht, one_mul]
    exact mul_right_cancel₀ h0 e

theorem positionOne_invariantIntegral_exchange_step (X T Y R : ℂ_[p]) (n : ℕ) (h1 : ‖T - X‖ ≤ (p : ℝ)⁻¹ ^ (n + 1))
    (h2 : ‖Y - R‖ ≤ (p : ℝ)⁻¹ ^ n) :
    ‖(X - (p : ℂ_[p]) * Y) - (T - (p : ℂ_[p]) * R)‖ ≤ (p : ℝ)⁻¹ ^ (n + 1) := by
  have e : (X - (p : ℂ_[p]) * Y) - (T - (p : ℂ_[p]) * R) = (X - T) - (p : ℂ_[p]) * (Y - R) := by ring
  rw [e, ← dist_eq_norm]
  refine (IsUltrametricDist.dist_triangle_max _ 0 _).trans (max_le ?_ ?_)
  · rw [dist_zero_right, norm_sub_rev]
    exact h1
  · rw [dist_zero_left, norm_mul, norm_p_cp, pow_succ']
    exact mul_le_mul_of_nonneg_left h2 (by positivity)

theorem approx (τ : K →+* ℂ_[p]) (cO : 𝓞 K →+* 𝓞 K)
    (hqn : ∀ (a : 𝓞 K) (n : ℕ), (p : 𝓞 K) ∣ a ^ ((p ^ 2) ^ n) - a)
    (hfrob : ∀ a : 𝓞 K, (p : 𝓞 K) ∣ cO a - a ^ p) (n : ℕ) (a : 𝓞 K) :
    ∃ r ∈ Subring.closure (gens p), ‖τ (a : K) - r.1‖ ≤ (p : ℝ)⁻¹ ^ n ∧
      ‖τ ((cO a : 𝓞 K) : K) - r.2‖ ≤ (p : ℝ)⁻¹ ^ n := by
  have hq1 : ∀ b : 𝓞 K, (p : 𝓞 K) ∣ b ^ (p ^ 2) - b := fun b => by simpa using hqn b 1
  let φ : 𝓞 K →+* ℂ_[p] := τ.comp (algebraMap (𝓞 K) K)
  induction n generalizing a with
  | zero =>
    refine ⟨0, zero_mem _, ?_, ?_⟩
    · simpa using norm_tau_le τ a
    · simpa using norm_tau_le τ (cO a)
  | succ n ih =>
    obtain ⟨c, hc⟩ := hqn a n
    obtain ⟨r', hr', h1, h2⟩ := ih (-c)
    set T := teich τ a with hT
    have hTc : teich τ (cO a) = T ^ p := teich_c τ hq1 a (cO a) (hfrob a)

    have rel1 : φ (a ^ ((p ^ 2) ^ n)) - φ a = (p : ℂ_[p]) * φ c := by
      have h := congrArg φ hc
      simpa only [map_sub, map_mul, map_natCast] using h
    have rel2 : φ (cO a ^ ((p ^ 2) ^ n)) - φ (cO a) = (p : ℂ_[p]) * φ (cO c) := by
      have h := congrArg (φ.comp cO) hc
      simpa only [RingHom.comp_apply, map_sub, map_mul, map_natCast, map_pow] using h
    have hn1 : φ (-c) = -φ c := map_neg φ c
    have hn2 : φ (cO (-c)) = -φ (cO c) := by rw [map_neg, map_neg]
    have k1 : ‖T - φ (a ^ ((p ^ 2) ^ n))‖ ≤ (p : ℝ)⁻¹ ^ (n + 1) := (teich_spec τ hq1 a).2 n
    have k2 : ‖T ^ p - φ (cO a ^ ((p ^ 2) ^ n))‖ ≤ (p : ℝ)⁻¹ ^ (n + 1) := by
      rw [← hTc]
      exact (teich_spec τ hq1 (cO a)).2 n
    have j1 : ‖r'.1 - φ (-c)‖ ≤ (p : ℝ)⁻¹ ^ n := by
      rw [norm_sub_rev]
      exact h1
    have j2 : ‖r'.2 - φ (cO (-c))‖ ≤ (p : ℝ)⁻¹ ^ n := by
      rw [norm_sub_rev]
      exact h2
    refine ⟨(T, T ^ p) + (p : ℂ_[p] × ℂ_[p]) * r', ?_, ?_, ?_⟩
    · exact Subring.add_mem _ (pair_mem_of_pow T (teich_pow τ hq1 a))
        (Subring.mul_mem _ (natCast_mem _ p) hr')
    · have s := positionOne_invariantIntegral_exchange_step _ _ _ _ n k1 j1
      have e : τ (a : K) - ((T, T ^ p) + (p : ℂ_[p] × ℂ_[p]) * r').1 =
          (φ (a ^ ((p ^ 2) ^ n)) - (p : ℂ_[p]) * r'.1) - (T - (p : ℂ_[p]) * φ (-c)) := by
        simp only [Prod.fst_add, Prod.fst_mul, Prod.fst_natCast]
        change φ a - _ = _
        rw [hn1]
        linear_combination -rel1
      rw [e]
      exact s
    · have s := positionOne_invariantIntegral_exchange_step _ _ _ _ n k2 j2
      have e : τ ((cO a : 𝓞 K) : K) - ((T, T ^ p) + (p : ℂ_[p] × ℂ_[p]) * r').2 =
          (φ (cO a ^ ((p ^ 2) ^ n)) - (p : ℂ_[p]) * r'.2) - (T ^ p - (p : ℂ_[p]) * φ (cO (-c))) := by
        simp only [Prod.snd_add, Prod.snd_mul, Prod.snd_natCast]
        change φ (cO a) - _ = _
        rw [hn2]
        linear_combination -rel2
      rw [e]
      exact s

end PI.OkpW
