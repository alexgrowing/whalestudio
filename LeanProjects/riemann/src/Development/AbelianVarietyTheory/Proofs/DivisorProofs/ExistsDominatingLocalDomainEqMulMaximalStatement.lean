import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominatingLocalDomainEqMulMaximal
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dominating_local_domain_eq_mul_maximal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (f G : R), G ∉ Ideal.span {f} → ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsLocalRing B) (_ : IsNoetherianRing B) (ι : R →+* B), Function.Injective ι ∧ IsLocalHom ι ∧ (∀ b : B, ∃ r : R, b - ι r ∈ maximalIdeal B) ∧ ∃ u ∈ maximalIdeal B, ι f = ι G * u := by
  first | exact @GlobalTheory.Izumi.exists_dominating_eq_mul_of_not_mem_span | exact GlobalTheory.Izumi.exists_dominating_eq_mul_of_not_mem_span | (intros; apply GlobalTheory.Izumi.exists_dominating_eq_mul_of_not_mem_span <;> assumption)
