import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

namespace GlobalTheory.GoodDepth

theorem not_dvd_discr_host : ∀ (Rk : Ranks) (H : Formalism.BasicNotions.Host Rk) (p : ℕ), p.Prime → p ∉ H.small →
    p ≠ H.q → p ≠ H.d → ¬ (p : ℤ) ∣ NumberField.discr H.E := by
  intro Rk H p hp hs hq hd hdvd
  have hc : p ∣ H.QS * H.q * H.d := H.der.discr_primes.1 p hp hdvd
  rcases (hp.dvd_mul).1 hc with h | h
  · rcases (hp.dvd_mul).1 h with h | h
    · exact hs (Nat.mem_primeFactors.2 ⟨hp, h, H.QS_pos.ne'⟩)
    · exact hq ((Nat.prime_dvd_prime_iff_eq hp H.hyp.1).1 h)
  · exact hd ((Nat.prime_dvd_prime_iff_eq hp H.hyp.2.1).1 h)

end GlobalTheory.GoodDepth
