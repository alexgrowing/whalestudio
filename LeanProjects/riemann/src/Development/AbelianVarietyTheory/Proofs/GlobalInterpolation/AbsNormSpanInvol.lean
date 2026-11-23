import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
import Formalism.LocalToGlobal.Columns.BaseLemmas

open NumberField IsDedekindDomain Formalism.L2.Col

namespace GlobalTheory.SplitUnram

variable {E : Type} [Field E] [NumberField E]

theorem absNorm_span_invol (s : 𝓞 E →+* 𝓞 E) (hs : ∀ x, s (s x) = x) (a : 𝓞 E) :
    Ideal.absNorm (Ideal.span {s a}) = Ideal.absNorm (Ideal.span {a}) := by
  let e : 𝓞 E ≃+* 𝓞 E := RingEquiv.ofRingHom s s (RingHom.ext hs) (RingHom.ext hs)
  let e' : 𝓞 E ≃ₐ[ℤ] 𝓞 E := AlgEquiv.ofRingEquiv (f := e) (fun n => by simp)
  rw [Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton]
  exact congrArg Int.natAbs (Algebra.norm_eq_of_algEquiv e' a)

theorem natCast_notMem_sq : ∀ (E : Type) [Field E] [NumberField E] (s : 𝓞 E →+* 𝓞 E) (a : 𝓞 E) (p : ℕ),
    (∀ x, s (s x) = x) → p.Prime → a * s a = (p : 𝓞 E) → IsCoprime a (s a) →
    2 * (divs a).card = Module.finrank ℚ E → (∀ P ∈ divs a, Ideal.absNorm P.asIdeal = p) →
    ∀ P ∈ divs a, ((p : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 := by
  intro E _ _ s a p hs hp ha hcop hcard hN P hP hmem
  classical
  have hp0 : (p : 𝓞 E) ≠ 0 := by exact_mod_cast hp.ne_zero
  have ha0 : a ≠ 0 := left_ne_zero_of_mul (ha ▸ hp0)
  have hnorm : Ideal.absNorm (Ideal.span {a}) = p ^ (divs a).card := by
    have h1 : Ideal.absNorm (Ideal.span {a}) ^ 2 = (p ^ (divs a).card) ^ 2 := by
      rw [← pow_mul, mul_comm, hcard, ← RingOfIntegers.rank, ← Ideal.absNorm_span_natCast, ← ha,
        ← Ideal.span_singleton_mul_span_singleton, map_mul, absNorm_span_invol s hs, sq]
    exact Nat.pow_left_injective two_ne_zero h1
  have haP : a ∈ P.asIdeal := (mem_divs ha0 P).1 hP
  have ha2 : a ∈ P.asIdeal ^ 2 := by
    obtain ⟨u, v, huv⟩ := hcop
    have h1 : a = u * a ^ 2 + v * (p : 𝓞 E) := by
      rw [← ha]
      linear_combination (-a) * huv
    rw [h1]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow haP 2)) (Ideal.mul_mem_left _ _ hmem)
  have hd1 : P.asIdeal ^ 2 ∣ Ideal.span {a} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact ha2
  have hd2 : ∏ Q ∈ (divs a).erase P, Q.asIdeal ∣ Ideal.span {a} := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro P _ Q _ hPQ
      exact (HeightOneSpectrum.isCoprime_of_ne P Q hPQ)
    · intro Q hQ
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact (mem_divs ha0 Q).1 (Finset.mem_of_mem_erase hQ)
  have hc : IsCoprime (P.asIdeal ^ 2) (∏ Q ∈ (divs a).erase P, Q.asIdeal) := by
    refine IsCoprime.pow_left (IsCoprime.prod_right fun Q hQ => ?_)
    exact HeightOneSpectrum.isCoprime_of_ne P Q (Finset.ne_of_mem_erase hQ).symm
  have hd := map_dvd Ideal.absNorm (hc.mul_dvd hd1 hd2)
  rw [hnorm, map_mul, map_pow, map_prod, hN P hP,
    Finset.prod_congr rfl (fun Q hQ => hN Q (Finset.mem_of_mem_erase hQ)), Finset.prod_const, ← pow_add,
    Nat.pow_dvd_pow_iff_le_right hp.one_lt] at hd
  have h3 := Finset.card_erase_add_one hP
  omega

end GlobalTheory.SplitUnram
