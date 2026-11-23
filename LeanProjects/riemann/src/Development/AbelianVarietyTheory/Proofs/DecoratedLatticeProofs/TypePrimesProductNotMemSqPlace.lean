import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypePrimeUnif

theorem mul_not_mem_sq {R : Type*} [CommRing R] [IsDedekindDomain R] (Q : HeightOneSpectrum R) {a b : R}
    (hab : IsCoprime a b) (ha : a ∈ Q.asIdeal → a ∉ Q.asIdeal ^ 2) (hb : b ∈ Q.asIdeal → b ∉ Q.asIdeal ^ 2) :
    a * b ∉ Q.asIdeal ^ 2 := by
  intro h
  have := Q.isPrime
  have hle : Q.asIdeal ^ 2 ≤ Q.asIdeal := Ideal.pow_le_self two_ne_zero
  rcases Ideal.IsPrime.mul_mem_pow Q.asIdeal h with h1 | h1
  · rcases Ideal.IsPrime.mul_mem_pow Q.asIdeal (mul_comm a b ▸ h) with h2 | h2
    · obtain ⟨u, v, huv⟩ := hab
      exact Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (huv ▸ Q.asIdeal.add_mem (Q.asIdeal.mul_mem_left u h1) (Q.asIdeal.mul_mem_left v h2)))
    · exact ha h1 h2
  · exact hb (hle h1) h1

theorem prod_not_mem_sq : ∀ (D : D7) (Q : Pl D.host.E), ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal ^ 2 := by
  intro D Q _
  have key : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal →
      ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal ^ 2 := fun k hk =>
    (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) Q hk).2.1
  have hc : Nat.Coprime (D.host.g 0) (D.host.g 1) :=
    (Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne
  rw [Nat.cast_mul]
  exact mul_not_mem_sq Q (Nat.Coprime.cast hc) (key 0) (key 1)

end GlobalTheory.TypePrimeUnif
