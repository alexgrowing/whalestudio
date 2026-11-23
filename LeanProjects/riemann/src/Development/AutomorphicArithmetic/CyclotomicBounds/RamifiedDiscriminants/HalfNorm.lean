import Development.AutomorphicArithmetic.PrimeDiscriminants.RamDiscr
import Development.AutomorphicArithmetic.FrobeniusLocalisation.halfSupp
import Development.AutomorphicArithmetic.FrobeniusLocalisation.CondRd
import Development.AutomorphicArithmetic.FrobeniusLocalisation.RamEq
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

open UpperTheory.HF

open NumberField Ideal
open scoped Pointwise

namespace Formalism.BasicNotions.Host

variable {R : Ranks} (H : Host R)

theorem not_dvd_discr_of_not_small {p : ℕ} (hp : p.Prime) (h2 : p ∉ H.small) (hq : p ≠ H.q) (hd : p ≠ H.d) :
    ¬ (p : ℤ) ∣ discr H.E := fun h => by
  rcases (H.toHostRaw.dvd_condN_iff_small hp).1 ((H.dvd_discr_iff_dvd_condN hp).1 h) with h | h | h
  exacts [h2 h, hq h, hd h]

theorem mem_ramI_iff {p : ℕ} (hp : p.Prime) : p ∈ H.toHostRaw.ramI ↔ p ∣ H.QS * H.q := by
  have h0 : (discr H.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero _)
  rw [Formalism.HC.HostRaw.ramI, Finset.mem_erase, Formalism.HC.HostRaw.ram, Nat.mem_primeFactors, H.dvd_natAbs_discr_iff hp]
  constructor
  · rintro ⟨hd, -, h, -⟩
    exact ((Nat.Prime.dvd_mul hp).1 h).resolve_right fun h' =>
      hd ((Nat.prime_dvd_prime_iff_eq hp H.toHostRaw.d_prime).1 h')
  · intro h
    refine ⟨?_, hp, h.mul_right _, h0⟩
    rintro rfl
    exact H.toHostRaw.d_not_dvd_QSq h

private theorem liesOver_of_mem {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 E)) [P.IsPrime]
    (h : (p : 𝓞 E) ∈ P) : P.LiesOver (span {(p : ℤ)}) :=
  ⟨Ideal.IsMaximal.eq_of_le
    (PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible)
    (Ideal.IsPrime.ne_top inferInstance) (by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]; exact h)⟩

private theorem mem_of_liesOver {E : Type} [Field E] [NumberField E] {p : ℕ} (P : Ideal (𝓞 E))
    (h : P.LiesOver (span {(p : ℤ)})) : (p : 𝓞 E) ∈ P := by
  have : (p : ℤ) ∈ P.under ℤ := by rw [← h.over]; exact Ideal.mem_span_singleton_self _
  simpa [Ideal.mem_comap] using this

private theorem dvd_absNorm_of {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (P J : Ideal (𝓞 E)) [hP : P.IsPrime]
    (h : (p : 𝓞 E) ∈ P) (hJ : P ∣ J) : p ∣ absNorm J := by
  by_contra hn
  obtain ⟨u, v, huv⟩ : IsCoprime (p : 𝓞 E) ((absNorm J : ℕ) : 𝓞 E) := ((Nat.Prime.coprime_iff_not_dvd hp).2 hn).cast
  exact hP.ne_top ((Ideal.eq_top_iff_one P).2
    (huv ▸ P.add_mem (P.mul_mem_left u h) (P.mul_mem_left v (Ideal.le_of_dvd hJ (Ideal.absNorm_mem J)))))

theorem half_ne_bot : H.𝔟 ≠ ⊥ := fun h => by
  have h1 := H.𝔟_spec.1
  rw [h, Ideal.bot_mul] at h1
  exact differentIdeal_ne_bot h1

theorem prime_dvd_absNorm_half_iff {p : ℕ} (hp : p.Prime) : p ∣ absNorm H.𝔟 ↔ p ∣ H.QS * H.q := by
  have hs := (UpperTheory.HF.half_supp H.toHostAx H.𝔟 H.𝔟_spec.1 H.𝔟_spec.2).1
  constructor
  · intro h
    obtain ⟨P, hP, hu, hd⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp _ h
    haveI := hP.isPrime
    obtain ⟨l, hl, ho⟩ := (hs P).1.1 (Or.inl hd)
    have hlp : l.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hl)
    have e : span {(l : ℤ)} = span {(p : ℤ)} := ho.over.trans hu
    have : p ∣ l := by
      have := Ideal.mem_span_singleton.1 (e ▸ Ideal.mem_span_singleton_self (l : ℤ))
      exact_mod_cast this
    rw [(Nat.prime_dvd_prime_iff_eq hp hlp).1 this]
    exact (H.mem_ramI_iff hlp).1 hl
  · intro h
    have h1 : p ∣ absNorm (span {(p : 𝓞 H.E)}) := by
      rw [Ideal.absNorm_span_natCast]
      exact dvd_pow_self _ Module.finrank_pos.ne'
    obtain ⟨P, hP, -, hd⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp _ h1
    haveI := hP.isPrime
    have hm : (p : 𝓞 H.E) ∈ P := Ideal.le_of_dvd hd (Ideal.mem_span_singleton_self _)
    rcases (hs P).1.2 ⟨p, (H.mem_ramI_iff hp).2 h, liesOver_of_mem hp P hm⟩ with h2 | h2
    · exact dvd_absNorm_of hp P _ hm h2
    · have hm' : (p : 𝓞 H.E) ∈ H.toHostRaw.conj • P := by
        have := Ideal.smul_mem_pointwise_smul H.toHostRaw.conj _ _ hm
        rwa [show H.toHostRaw.conj • (p : 𝓞 H.E) = p from map_natCast (MulSemiringAction.toRingHom _ (𝓞 H.E) H.toHostRaw.conj) p] at this
      exact dvd_absNorm_of hp _ _ hm' h2

theorem four_ord_le_condN : 4 * R.toFrame.ord ≤ H.QS * H.q * H.d := by
  have h := UpperTheory.HF.cond_rd H.toHostAx
  have h2 := UpperTheory.HF.ram_eq H.toHostAx
  refine h.2.2.2.2.2.2.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero H.toHostRaw.condN_ne_zero) ?_)
  rw [h2.2.2.2.1]
  refine Nat.mul_dvd_mul_right (Nat.mul_dvd_mul h2.2.2.2.2.1 ?_) _
  split_ifs
  exacts [dvd_rfl, one_dvd _]

theorem condN_le_four_sq : ((H.QS : ℝ) * H.q * H.d) ≤ 4 * (R.n : ℝ) ^ 2 * H.q * H.d := by
  have h : (H.QS : ℝ) ≤ (R.n : ℝ) ^ 2 := by exact_mod_cast H.QS_le
  have h0 : (0 : ℝ) ≤ (R.n : ℝ) ^ 2 := by positivity
  gcongr
  linarith

end Formalism.BasicNotions.Host
