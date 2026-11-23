import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.UnitriangularFrameLift
import Lemmata.GeneralBFactUpperVersion.Imports

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open NumberField IsDedekindDomain

theorem iroot_mem {R : Type} [CommRing R] [IsDomain R] (ζ : R) (M : ℕ) (P : Ideal R) (h1 : ζ ≠ 1) (hM : ζ ^ M = 1)
    (hP : ζ - 1 ∈ P) : (M : R) ∈ P := by
  first | exact Bl.general_b_fact_upper_version.goal1 .. | (apply Bl.general_b_fact_upper_version.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_upper_version.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper_version.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_upper_version.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper_version.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› ‹_› ζ M P h1 hM hP | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› ‹_› ζ M P h1 hM | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› ‹_› ζ M P h1 | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› ‹_› ζ M P | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› ‹_› ζ M | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› ‹_› ζ | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› ‹_› | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› | exact @Bl.general_b_fact_upper_version.goal1 R

theorem id_root : RootsOfUnityFormal := by
  intro R _ _ ζ N g1 g2 P1 P2 hN hζN hg1 hg2 hne hP1 hP2 h1 h2 hz1 hz2
  by_contra hζ
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨N, hN, hζN⟩
  have hMpos : 0 < orderOf ζ := orderOf_pos_iff.2 hfin
  have hM1 : ((orderOf ζ : ℕ) : R) ∈ P1 := iroot_mem ζ _ P1 hζ (pow_orderOf_eq_one ζ) hz1
  have hdvd : g1 ∣ orderOf ζ := by
    by_contra hnd
    exact id_coprime_notMem P1 hP1 g1 _ ((Nat.Prime.coprime_iff_not_dvd hg1).2 hnd) h1 hM1
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    omega
  have hklt : k < orderOf ζ := by
    rw [hk]
    have := hg1.two_le
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    nlinarith
  have hη : ζ ^ k ≠ 1 := pow_ne_one_of_lt_orderOf hk0 hklt
  have hηg : (ζ ^ k) ^ g1 = 1 := by
    rw [← pow_mul, mul_comm, ← hk]
    exact pow_orderOf_eq_one ζ
  have hηP : ζ ^ k - 1 ∈ P2 := by
    obtain ⟨w, hw⟩ := sub_dvd_pow_sub_pow ζ 1 k
    rw [one_pow] at hw
    rw [hw]
    exact P2.mul_mem_right _ hz2
  have hg1P2 : (g1 : R) ∈ P2 := iroot_mem (ζ ^ k) g1 P2 hη hηg hηP
  exact id_coprime_notMem P2 hP2 g2 g1 ((Nat.coprime_primes hg2 hg1).2 hne.symm) h2 hg1P2

theorem id_over : ExistsPrimeAbove := by
  intro E _ _ p hp
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    (Ideal.span_singleton_prime (Int.natCast_ne_zero.2 hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp) |>.isMaximal
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact Int.natCast_ne_zero.2 hp.ne_zero)
  obtain ⟨Q, hQ, hc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) (Ideal.span {(p : ℤ)}) (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective ℤ (𝓞 E))]
    exact bot_le)
  have hpQ : (p : 𝓞 E) ∈ Q := by
    have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := by
      rw [hc]; exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ.isPrime, ?_⟩, hpQ⟩
  rintro rfl
  exact (Nat.cast_ne_zero.2 hp.ne_zero) ((Submodule.mem_bot _).1 hpQ)

end Formalism.MainNotions.BridgeLemma

end
