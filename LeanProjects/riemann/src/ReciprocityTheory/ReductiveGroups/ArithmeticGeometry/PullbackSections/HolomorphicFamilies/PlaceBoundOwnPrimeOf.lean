import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIntegralUnramified

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj

theorem not_both_mem {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {a b : ℕ}
    (hab : Nat.Coprime a b) (ha : (a : 𝓞 K) ∈ la.asIdeal) (hb : (b : 𝓞 K) ∈ la.asIdeal) : False := by
  have hg := Nat.gcd_eq_gcd_ab a b
  have h1 : ((Nat.gcd a b : ℕ) : ℤ) = 1 := by rw [hab]; rfl
  have e : (1 : 𝓞 K) = (a : 𝓞 K) * ((Nat.gcdA a b : ℤ) : 𝓞 K) + (b : 𝓞 K) * ((Nat.gcdB a b : ℤ) : 𝓞 K) := by
    have : ((1 : ℤ) : 𝓞 K) = (((a : ℤ) * Nat.gcdA a b + (b : ℤ) * Nat.gcdB a b : ℤ) : 𝓞 K) := by
      rw [← hg, h1]
    push_cast at this
    exact this
  have hone : (1 : 𝓞 K) ∈ la.asIdeal := by
    rw [e]
    exact la.asIdeal.add_mem (la.asIdeal.mul_mem_right _ ha) (la.asIdeal.mul_mem_right _ hb)
  exact la.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hone)

theorem vLa_nat_nonneg {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (p : ℕ) :
    0 ≤ vLa la (p : K) := by
  by_cases hp : (p : K) = 0
  · simp [vLa, hp]
  unfold vLa
  have e : (p : K) = ((p : 𝓞 K) : K) := by simp
  rw [e] at hp ⊢
  have h1 := la.valuation_le_one (K := K) (p : 𝓞 K)
  have h2 : (la.valuation K) ((p : 𝓞 K) : K) ≠ 0 := (Valuation.ne_zero_iff _).mpr hp
  have h3 := (WithZero.log_le_log h2 one_ne_zero).mpr h1
  rw [WithZero.log_one] at h3
  omega

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
