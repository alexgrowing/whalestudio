import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotKernelIdealEqBeyondExponentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHopfAlgebraEqRangeMulKernelStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem finrank_A_eq {p : ℕ} {k : Type} [Field k] (G : PDivGroup p k) (n : ℕ) :
    Module.finrank k (G.A n) = p ^ (n * G.height) := by
  have h := G.rank_eq n ⟨⊥, Ideal.isPrime_bot⟩
  rwa [Module.rankAtStalk_eq_finrank_of_free] at h

theorem existsUnique_hasLogDeg : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G Q : PDivGroup p k)
    (q : G ⟶ Q), IsIsog q → ∃! e : ℕ, HasLogDeg q e := by
  intro p _ k _ _ G Q q hq
  have hp : p.Prime := Fact.out
  obtain ⟨n, q', h1, -⟩ := hq
  have hlag := GlobalTheory.T.finrank_hopfAlgebra_eq_range_mul_kernel k (G.A n) (Q.A n) (q.app n)
  rw [finrank_A_eq] at hlag
  have hdvd : Module.finrank k (G.A n ⧸ kerIdeal (q.app n)) ∣ p ^ (n * G.height) :=
    ⟨_, hlag.trans (mul_comm _ _)⟩
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  refine ⟨e, ⟨n, fun m hm => (GlobalTheory.T.finrank_quot_kernelIdeal_eq_beyond_exponent p k G Q n m q q' h1 hm).trans he⟩, ?_⟩
  rintro e' ⟨N, hN⟩
  have h2 := hN (max N n) (le_max_left _ _)
  rw [GlobalTheory.T.finrank_quot_kernelIdeal_eq_beyond_exponent p k G Q n (max N n) q q' h1 (le_max_right _ _), he] at h2
  exact Nat.pow_right_injective hp.two_le h2.symm

end GlobalTheory.Dieu
