import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceBoundOddRamifiedOfCharts

noncomputable section

namespace GlobalTheory.RamValCheck

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.PullbackSections

theorem g_coprime (D : D7) (k : Fin 2) (p : ℕ) (hp : p ∈ D.host.condN.primeFactors) :
    Nat.Coprime (D.host.g k) p := by
  have hc := D.ntypes.g_cond k
  have hdvd : p ∣ D.host.QS * D.host.q * D.host.d := Nat.dvd_of_mem_primeFactors hp
  refine Nat.Coprime.coprime_dvd_right hdvd ?_
  rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hc]
  simp

theorem one_le_vLa {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (p : ℕ) (hp : p ≠ 0)
    (hla : (p : 𝓞 K) ∈ la.asIdeal) : 1 ≤ vLa la (p : K) := by
  have h0 : (p : K) ≠ 0 := by exact_mod_cast hp
  have hv : la.valuation K (p : K) < 1 := by
    have := (la.valuation_lt_one_iff_mem (K := K) (p : 𝓞 K)).2 hla
    simpa using this
  have hne : la.valuation K (p : K) ≠ 0 := (la.valuation K).ne_zero_iff.2 h0
  have := (WithZero.log_lt_log hne one_ne_zero).2 hv
  simp only [WithZero.log_one] at this
  unfold vLa
  omega

end GlobalTheory.RamValCheck
