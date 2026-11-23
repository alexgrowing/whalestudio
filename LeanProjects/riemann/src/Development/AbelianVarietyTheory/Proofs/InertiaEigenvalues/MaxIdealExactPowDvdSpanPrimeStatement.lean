import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxIdealExactPowDvdSpanPrime
import Mathlib
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_span_prime_eq_pow_mul_coprime : ∀ (L : Type) [Field L] [NumberField L] (l e : ℕ), l.Prime → ∀ (la : Ideal (𝓞 L)) [la.IsMaximal], ((l : ℕ) : 𝓞 L) ∈ la → ((l : ℕ) : 𝓞 L) ∉ la ^ (e + 1) → ∃ (e' : ℕ) (J : Ideal (𝓞 L)), 0 < e' ∧ e' ≤ e ∧ la ⊔ J = ⊤ ∧ Ideal.span {((l : ℕ) : 𝓞 L)} = la ^ e' * J := by
  first | exact @GlobalTheory.maxIdeal_exact_pow_dvd_span_prime | exact GlobalTheory.maxIdeal_exact_pow_dvd_span_prime | (intros; apply GlobalTheory.maxIdeal_exact_pow_dvd_span_prime <;> assumption)
