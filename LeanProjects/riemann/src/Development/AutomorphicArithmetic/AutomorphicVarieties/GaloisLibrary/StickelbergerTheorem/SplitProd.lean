import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.ImportsBis
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.SplitInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt

open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick
open scoped nonZeroDivisors

theorem UpperTheory.V.Stick.splitProd :
    ∀ (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (p : ℕ) [Fact p.Prime] (π : 𝓞 K →+* ZMod p), p.Coprime M →
    (∀ t, Prime (conjI M K (RingHom.ker π) t)) ∧ ∏ t, conjI M K (RingHom.ker π) t = Ideal.span {(p : 𝓞 K)} := by
  intro M _ K _ _ _ p _ π hcop
  classical
  have hker : ∀ t, conjI M K (RingHom.ker π) t = RingHom.ker (π.comp (sgO M K t : 𝓞 K →+* 𝓞 K)) := by
    intro t
    ext x
    simp [conjI, RingHom.mem_ker]
  have hfact : ∀ t, Ideal.absNorm (conjI M K (RingHom.ker π) t) = p ∧ (conjI M K (RingHom.ker π) t).IsMaximal ∧
      Prime (conjI M K (RingHom.ker π) t) ∧ (p : 𝓞 K) ∈ conjI M K (RingHom.ker π) t := fun t =>
    (red K p (conjI M K (RingHom.ker π) t)).2 _ (hker t).symm
  refine ⟨fun t => (hfact t).2.2.1, ?_⟩
  have hinj := splitInj M K p π hcop
  have hdvd : ∏ t, conjI M K (RingHom.ker π) t ∣ Ideal.span {(p : 𝓞 K)} := by
    apply Fintype.prod_dvd_of_coprime
    · intro s t hst
      haveI := (hfact s).2.1
      haveI := (hfact t).2.1
      exact Ideal.isCoprime_of_isMaximal (fun h => hst (hinj h))
    · intro t
      rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
      exact (hfact t).2.2.2
  obtain ⟨Q, hQ⟩ := hdvd
  have hfr : Module.finrank ℚ K = M.totient :=
    IsCyclotomicExtension.finrank K (Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_ne_zero (NeZero.ne M)))
  have hnp : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ M.totient := by
    rw [Ideal.absNorm_span_singleton]
    have e : ((p : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) := by simp
    rw [e, Algebra.norm_algebraMap, RingOfIntegers.rank, hfr]
    simp [Int.natAbs_pow]
  have hnprod : Ideal.absNorm (∏ t, conjI M K (RingHom.ker π) t) = p ^ M.totient := by
    rw [map_prod, Finset.prod_congr rfl (fun t _ => (hfact t).1), Finset.prod_const, Finset.card_univ,
      ZMod.card_units_eq_totient]
  have hQ1 : Ideal.absNorm Q = 1 := by
    have h := congrArg Ideal.absNorm hQ
    rw [map_mul, hnp, hnprod] at h
    have hp0 : p ^ M.totient ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp0) (h.symm.trans (mul_one _).symm)
  rw [Ideal.absNorm_eq_one_iff] at hQ1
  rw [hQ, hQ1, Ideal.mul_top]
