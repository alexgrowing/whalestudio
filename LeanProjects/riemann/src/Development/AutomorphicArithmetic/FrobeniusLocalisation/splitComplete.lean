import Development.AutomorphicArithmetic.FrobeniusLocalisation.SizeDefs
import Development.AutomorphicArithmetic.FrobeniusLocalisation.FrobGSpec
import Development.AutomorphicArithmetic.FrobeniusLocalisation.FrobDecomp

open UpperTheory.HF

open NumberField IntermediateField Ideal Formalism.FrobeniusOrbits Formalism.HC
open scoped Pointwise

theorem UpperTheory.HF.split_complete :
    ∀ (φ : Frame) (H : HostAx φ) (p : ℕ), p.Prime → p ≡ 1 [MOD H.condN] →
      ¬ p ∣ H.condN ∧ H.frobG p = 1 ∧ jacobiSym (-(H.d : ℤ)) p = 1 ∧ H.condN < p ∧ 16 * H.d * H.q ∣ p - 1 ∧
      (primesOver (span {(p : ℤ)}) (𝓞 H.E)).ncard = 4 * φ.ord := by
  intro φ H p hp h1
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : H.condN ∣ p - 1 := (Nat.modEq_iff_dvd' hp.one_le).1 h1.symm
  have h2 := hp.two_le
  have hlt : H.condN < p := by
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hnd : ¬ p ∣ H.condN := fun h => absurd (Nat.le_of_dvd H.condN_pos h) (by omega)
  have hc : Nat.Coprime p H.condN := hp.coprime_iff_not_dvd.2 hnd
  have hfrob : H.frobG p = 1 := by
    rw [H.frobG_of_coprime hc]
    have hu : ZMod.unitOfCoprime p hc = 1 := by
      apply Units.ext
      rw [ZMod.coe_unitOfCoprime, Units.val_one, (ZMod.natCast_eq_natCast_iff _ _ _).2 h1, Nat.cast_one]
    rw [hu, map_one]
  refine ⟨hnd, hfrob, ?_, hlt, ?_, ?_⟩
  · refine (UpperTheory.HF.frobG_spec φ H p hnd).2.2.2.2.1.1 ?_
    rw [hfrob]
    exact one_mem _
  · refine Dvd.dvd.trans ?_ hdvd
    rw [mul_right_comm]
    exact Nat.mul_dvd_mul_right (Nat.mul_dvd_mul_right H.sixteen_dvd_QS _) _
  · haveI : (span {(p : ℤ)}).IsPrime :=
      (span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
    obtain ⟨⟨P, hP1, hP2⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 H.E) (span {(p : ℤ)})
    have h := (UpperTheory.HF.frob_decomp φ H p hnd P).2.2
    rwa [hfrob, orderOf_one, mul_one] at h
