import Formalism.LocalRingCardinality.DataHost
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

namespace Formalism.BasicNotions.Host

variable {R : Ranks} (H : Host R)

theorem dvd_condN_iff_cls {p : ℕ} (hp : p.Prime) :
    p ∣ H.condN ↔ H.cls p = .ram2 ∨ H.cls p = .ramQ ∨ H.cls p = .ramD := by
  have key : H.cls p = .ram2 ∨ H.cls p = .ramQ ∨ H.cls p = .ramD ↔ p ∈ H.small ∨ p = H.q ∨ p = H.d := by
    unfold Host.cls primeClass
    split_ifs <;> simp_all
  obtain ⟨hqp, hdp, -, -, -⟩ := H.hyp
  have hQS : H.QS ≠ 0 := H.QS_pos.ne'
  have hs : p ∣ H.QS ↔ p ∈ H.small := by
    show p ∣ H.QS ↔ p ∈ H.QS.primeFactors
    rw [Nat.mem_primeFactors]
    exact ⟨fun h => ⟨hp, h, hQS⟩, fun h => h.2.1⟩
  rw [key, show H.condN = H.QS * H.q * H.d from rfl, hp.dvd_mul, hp.dvd_mul, Nat.prime_dvd_prime_iff_eq hp hqp,
    Nat.prime_dvd_prime_iff_eq hp hdp, hs, or_assoc]

theorem not_inert_of_dvd {p : ℕ} (hp : p.Prime) (h : p ∣ H.condN) :
    ¬ (H.cls p = .inertClass ∨ H.cls p = .signal) := by
  rcases (dvd_condN_iff_cls H hp).mp h with h1 | h1 | h1 <;> rw [h1] <;> simp

end Formalism.BasicNotions.Host
