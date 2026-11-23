import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdxEqRelIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise

namespace GlobalTheory.InertResidue

theorem card_of_involution {k : Type} [Field k] [Finite k] {q : ℕ} [Fact q.Prime] [CharP k q] (s : k →+* k)
    (hs : ∀ x, s (s x) = x) {r : k} {m : ℤ} (hr : r ^ 2 = m) (hsr : s r = -r) (hne : -r ≠ r) :
    (∃ f, Odd f ∧ Nat.card k = q ^ (2 * f)) ∧ ¬ IsSquare (m : ZMod q) := by
  letI : Algebra (ZMod q) k := ZMod.algebra k q
  haveI := Fintype.ofFinite k
  let σ : k ≃ₐ[ZMod q] k :=
    { toFun := s, invFun := s, left_inv := hs, right_inv := hs, map_mul' := map_mul s, map_add' := map_add s,
      commutes' := fun c => RingHom.congr_fun (Subsingleton.elim (s.comp (algebraMap (ZMod q) k)) _) c }
  have hσ : ∀ x, σ x = s x := fun _ => rfl
  constructor
  · obtain ⟨⟨j, hj⟩, e⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod q) k).2 σ
    set φ := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod q) k with hφ
    change φ ^ j = σ at e
    have ho : orderOf φ = Module.finrank (ZMod q) k := FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod q) k
    have h2 : φ ^ (2 * j) = 1 := by
      rw [two_mul, pow_add, e]; ext x; exact hs x
    have hsq : (φ r) ^ 2 = r ^ 2 := by rw [← map_pow, hr, map_intCast]
    have hev : ∀ i, (φ ^ (2 * i)) r = r := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih =>
        rw [mul_add, pow_add, AlgEquiv.mul_apply, mul_one, sq, AlgEquiv.mul_apply]
        rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
        · rw [h, h, ih]
        · rw [h, map_neg, h, neg_neg, ih]
    have hodd : Odd j := by
      rcases Nat.even_or_odd' j with ⟨i, rfl | rfl⟩
      · exact absurd (by rw [← hsr, ← hσ, ← e, hev]) hne
      · exact ⟨i, rfl⟩
    refine ⟨j, hodd, ?_⟩
    have hd := orderOf_dvd_of_pow_eq_one h2
    rw [ho] at hd
    have hn : Module.finrank (ZMod q) k = 2 * j := by
      obtain ⟨c, hc⟩ := hd
      have hj0 := hodd.pos
      rcases c with _ | _ | c
      · omega
      · omega
      · nlinarith [Nat.zero_le (Module.finrank (ZMod q) k * c)]
    rw [Module.natCard_eq_pow_finrank (K := ZMod q), hn, Nat.card_zmod]
  · rintro ⟨c, hc⟩
    have h1 : r ^ 2 = (algebraMap (ZMod q) k c) ^ 2 := by rw [hr, sq, ← map_mul, ← hc, map_intCast]
    apply hne
    rw [← hsr, ← hσ]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h <;> rw [h] <;> simp

theorem exists_root (D : D7) (n : ℕ) (b : D.host.E) (hb : b ^ 2 = -(n : D.host.E)) :
    ∃ r : 𝓞 D.host.E, r ^ 2 = ((-(n : ℤ) : ℤ) : 𝓞 D.host.E) ∧ D.host.conj • r = -r := by
  have hint : IsIntegral ℤ b := by
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [hb]
    exact (isIntegral_natCast n).neg
  have hconj : D.host.conj b = -b := by
    apply D.host.φ₀.injective
    have h1 : D.host.φ₀ (D.host.conj b) = starRingEnd ℂ (D.host.φ₀ b) :=
      D.host.conjE_apply D.host.φ₀ b
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have h2 : (D.host.φ₀ b) ^ 2 = (Complex.I * (Real.sqrt n : ℂ)) ^ 2 := by
      rw [← map_pow, hb, map_neg, map_natCast, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
        Real.sq_sqrt hn0]
      simp
    rw [h1, map_neg]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h <;> rw [h] <;> simp
  refine ⟨⟨b, hint⟩, RingOfIntegers.ext ?_, RingOfIntegers.ext hconj⟩
  have : (((-(n : ℤ) : ℤ) : 𝓞 D.host.E) : D.host.E) = ((-(n : ℤ) : ℤ) : D.host.E) :=
    map_intCast (algebraMap (𝓞 D.host.E) D.host.E) _
  rw [this]
  push_cast
  exact hb

theorem two_not_mem (D : D7) {P : Ideal (𝓞 D.host.E)} (hP : P.IsPrime) (hsP : ∀ x ∈ P, D.host.conj • x ∈ P) :
    (2 : 𝓞 D.host.E) ∉ P := by
  intro h2
  have hw : D.host.conj • (Formalism.L2.Pj.w0E D) = 1 - Formalism.L2.Pj.w0E D := by
    rw [← Formalism.L2.Pj.conj_w0E D]
    exact RingOfIntegers.ext (Formalism.L2.Pj.barE_eq_conj D (Formalism.L2.Pj.w0E D)).symm
  have hsq := Formalism.L2.Pj.w0E_sq D
  obtain ⟨k, hk⟩ : ∃ k, Formalism.L2.Pj.mE D = 2 * k := by
    have h1 := D.host.hyp.2.2.2.1
    have h3 := Formalism.L2.Pj.mE_spec D
    exact ⟨Formalism.L2.Pj.mE D / 2, by omega⟩
  rw [hk] at hsq
  push_cast at hsq
  set w := Formalism.L2.Pj.w0E D
  have hm : w * (1 - w) ∈ P := by
    have : w * (1 - w) = k * 2 := by linear_combination -hsq
    rw [this]; exact P.mul_mem_left _ h2
  apply hP.ne_top
  rw [Ideal.eq_top_iff_one]
  rcases hP.mem_or_mem hm with h | h
  · have h' := hsP _ h
    rw [hw] at h'
    simpa using P.add_mem h h'
  · have h' := hsP _ h
    rw [smul_sub, smul_one, hw] at h'
    simpa using P.add_mem h h'

theorem card_of_root (D : D7) {P : Ideal (𝓞 D.host.E)} (hP : P.IsMaximal) (hfix : D.host.conj • P = P) {q : ℕ}
    (hq : q.Prime) (hqP : (q : 𝓞 D.host.E) ∈ P) (n : ℕ) (hc : Nat.Coprime q n) (b : D.host.E)
    (hb : b ^ 2 = -(n : D.host.E)) :
    (∃ f, Odd f ∧ Ideal.absNorm P = q ^ (2 * f)) ∧ ¬ IsSquare (-(n : ZMod q)) := by
  have hsP : ∀ x ∈ P, D.host.conj • x ∈ P := fun x hx => by
    rw [← hfix]; exact Ideal.smul_mem_pointwise_smul _ _ _ hx
  obtain ⟨r, hr, hsr⟩ := exists_root D n b hb
  haveI := Fact.mk hq
  letI := Ideal.Quotient.field P
  haveI : Finite (𝓞 D.host.E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P
    (Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _))
  haveI : CharP (𝓞 D.host.E ⧸ P) q := (CharP.charP_iff_prime_eq_zero hq).2 (by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]; exact hqP)
  let c := MulSemiringAction.toRingHom _ (𝓞 D.host.E) D.host.conj
  let s : 𝓞 D.host.E ⧸ P →+* 𝓞 D.host.E ⧸ P := Ideal.quotientMap P c hsP
  have hs : ∀ x, s (Ideal.Quotient.mk P x) = Ideal.Quotient.mk P (D.host.conj • x) := fun _ => rfl
  have h := card_of_involution (q := q) s (r := Ideal.Quotient.mk P r) (m := -(n : ℤ))
    (fun x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [hs, hs, smul_smul, VacInt.conj_mul_self, one_smul])
    (by rw [← map_pow, hr, map_intCast]) (by rw [hs, hsr, map_neg])
    (fun h => by
      rw [← map_neg, Ideal.Quotient.eq] at h
      have h2 : 2 * r ∈ P := by
        have := P.neg_mem h
        convert this using 1
        ring
      have h3 := (hP.isPrime.mem_or_mem h2).resolve_left (two_not_mem D hP.isPrime hsP)
      have hnP : (n : 𝓞 D.host.E) ∈ P := by
        have := P.neg_mem (hr ▸ P.pow_mem_of_mem h3 2 two_pos)
        simpa using this
      obtain ⟨u, v, huv⟩ : IsCoprime (q : 𝓞 D.host.E) (n : 𝓞 D.host.E) := hc.cast
      exact hP.ne_top ((Ideal.eq_top_iff_one P).2
        (huv ▸ P.add_mem (P.mul_mem_left u hqP) (P.mul_mem_left v hnP))))
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  push_cast at h
  exact h

theorem exists_prime (D : D7) {P : Ideal (𝓞 D.host.E)} (hP : P.IsMaximal) :
    ∃ q n : ℕ, q.Prime ∧ (q : 𝓞 D.host.E) ∈ P ∧ Ideal.absNorm P = q ^ n := by
  letI := Ideal.Quotient.field P
  haveI : Finite (𝓞 D.host.E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P
    (Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _))
  haveI := Fintype.ofFinite (𝓞 D.host.E ⧸ P)
  obtain ⟨q, hc, n, hq, hn⟩ := FiniteField.card' (𝓞 D.host.E ⧸ P)
  refine ⟨q, n, hq, ?_, ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ q
  · rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, hn]

theorem norm_prime : ∀ (D : D7) (P : Ideal (𝓞 D.host.E)), P.IsMaximal → Ev D (Ideal.absNorm P) ∧ (D.host.conj • P = P → sgn D (Ideal.absNorm P) = -1 ∧ ∃ q f : ℕ, q.Prime ∧ InertQ D q ∧ q ≠ 2 ∧ (q : 𝓞 D.host.E) ∈ P ∧ Odd f ∧ Ideal.absNorm P = q ^ (2 * f) ∧ (q ≠ D.host.d → ¬ IsSquare (-(D.host.d : ZMod q)))) ∧ (D.host.conj • P ≠ P → sgn D (Ideal.absNorm P) = 1 ∧ ∀ q : ℕ, q.Prime → (q : 𝓞 D.host.E) ∈ P → ¬ InertQ D q) := by
  intro D P hP
  obtain ⟨q, n, hq, hqP, hn⟩ := exists_prime D hP
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
  by_cases hfix : D.host.conj • P = P
  · have hin : InertQ D q := by
      by_contra h
      exact VacInt.conj_smul_ne D hq h P hP.isPrime hqP hfix
    obtain ⟨hq₁, hd, hq8, hd16, -⟩ := D.host.hyp
    have hd' : q ≠ D.host.d → _ := fun h => card_of_root D hP hfix hq hqP D.host.d
      ((Nat.coprime_primes hq hd).2 h) (D.host.sqd)
      (D.host.sqd_sq)
    obtain ⟨f, hf, hN⟩ : ∃ f, Odd f ∧ Ideal.absNorm P = q ^ (2 * f) := by
      by_cases h : q = D.host.d
      · exfalso
        haveI := hP.isPrime
        haveI : P.LiesOver (Ideal.span {(q : ℤ)}) := by
          refine ⟨Ideal.IsMaximal.eq_of_le
            (PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hq).irreducible)
            (Ideal.IsPrime.ne_top inferInstance) ?_⟩
          rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
          exact hqP
        exact D.host.der.decompConj q hq (h ▸ Dvd.intro_left _ rfl) P (MulAction.mem_stabilizer_iff.2 hfix)
      · exact (hd' h).1
    refine ⟨?_, fun _ => ⟨?_, q, f, hq, hin, ?_, hqP, hf, hN, fun h => (hd' h).2⟩, fun h => absurd hfix h⟩
    · intro p _ _
      rw [hN, Nat.factorization_pow]
      simp [Nat.even_mul]
    · have hf0 : 2 * f ≠ 0 := by have := hf.pos; omega
      rw [hN, sgn, hlf, Nat.primeFactors_prime_pow hf0 hq, Finset.filter_singleton, if_pos hin,
        Finset.sum_singleton, Nat.factorization_pow_self hq, Nat.mul_div_cancel_left _ two_pos, hf.neg_one_pow]
    · rintro rfl
      exact two_not_mem D hP.isPrime
        (fun x hx => by rw [← hfix]; exact Ideal.smul_mem_pointwise_smul _ _ _ hx) (by exact_mod_cast hqP)
  · have hall : ∀ p : ℕ, (p : 𝓞 D.host.E) ∈ P → ¬ InertQ D p := fun p hp h => hfix (h P hP.isPrime hP0 hp)
    have h0 : ∀ p : ℕ, InertQ D p → (Ideal.absNorm P).factorization p = 0 := fun p hp => by
      rw [hn, hq.factorization_pow, Finsupp.single_eq_of_ne]
      rintro rfl
      exact hall _ hqP hp
    refine ⟨fun p _ hp => by rw [h0 p hp]; exact Even.zero, fun h => absurd h hfix, fun _ => ⟨?_, fun p _ hp => hall p hp⟩⟩
    rw [← sgn_one (D := D)]
    exact sgn_congr fun p _ hp => by rw [h0 p hp]; simp

end GlobalTheory.InertResidue
