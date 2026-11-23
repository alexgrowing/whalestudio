import Mathlib
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.DataMink
import Formalism.LocalRingCardinality.DataErr
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
open NumberField Formalism.BasicNotions

namespace GlobalTheory

theorem prime_le_succ_of_dvd_minkM : ∀ n p : ℕ, p.Prime → p ∣ minkM n → p ≤ n + 1 := by
  intro n p hp h
  unfold minkM Formalism.HermitianLatticeCounting.S6.minkowskiM at h
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finset_prod_iff hp.prime _).1 h
  rw [Finset.mem_filter, Finset.mem_range] at hq
  have h1 : p = q := (Nat.prime_dvd_prime_iff_eq hp hq.2).1 (hp.dvd_of_dvd_pow hpq)
  omega

end GlobalTheory
