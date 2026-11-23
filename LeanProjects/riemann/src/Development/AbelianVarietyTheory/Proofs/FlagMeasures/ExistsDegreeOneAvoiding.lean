import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.SArith
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsGoodSplitPrimeCmField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotDvdDiscrIffRamificationIdx

open NumberField Polynomial

namespace GlobalTheory.LargeSplitPrime

theorem exists_degree_one_avoiding (N : Type) [Field N] [NumberField N] (m : ℤ) (hm : m ≠ 0) :
    ∃ P : Ideal (𝓞 N), P.IsMaximal ∧ (m : 𝓞 N) ∉ P ∧ Function.Surjective (Int.castRingHom (𝓞 N ⧸ P)) := by
  obtain ⟨θ, d, hd, -, hden⟩ := GlobalTheory.SW.SplitPrime.exists_prim_den N
  by_cases hθ : θ = 0
  · refine GlobalTheory.SW.SplitPrime.exists_degree_one (1 : 𝓞 N) one_ne_zero d hd (fun a => ?_) m hm
    obtain ⟨g, hg⟩ := hden a
    refine ⟨C (g.coeff 0), ?_⟩
    rw [hg, hθ, aeval_C, aeval_def, eval₂_at_zero]
  · exact GlobalTheory.SW.SplitPrime.exists_degree_one θ hθ d hd hden m hm

theorem surjective_of_conj {N : Type} [Field N] [NumberField N] [IsGalois ℚ N] {p : ℕ} (hp : p.Prime)
    (P Q : Ideal (𝓞 N)) [hP : P.IsMaximal] [hQ : Q.IsMaximal] (h1 : (p : 𝓞 N) ∈ P) (h2 : (p : 𝓞 N) ∈ Q)
    (hs : Function.Surjective (Int.castRingHom (𝓞 N ⧸ P))) :
    Function.Surjective (Int.castRingHom (𝓞 N ⧸ Q)) := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have : P.LiesOver (Ideal.span {(p : ℤ)}) := (Ideal.liesOver_span_iff hP.ne_top hp').mpr (by simpa using h1)
  have : Q.LiesOver (Ideal.span {(p : ℤ)}) := (Ideal.liesOver_span_iff hQ.ne_top hp').mpr (by simpa using h2)
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P Q (N ≃ₐ[ℚ] N)
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨t, ht⟩ := hs (Ideal.Quotient.mk P (σ⁻¹ • a))
  have h3 : (t : 𝓞 N) - σ⁻¹ • a ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← ht]; simp
  have h4 : σ • ((t : 𝓞 N) - σ⁻¹ • a) ∈ Q := hσ ▸ Ideal.smul_mem_pointwise_smul σ _ _ h3
  have h5 : σ • (t : 𝓞 N) = t := map_intCast (MulSemiringAction.toRingHom _ _ σ) t
  rw [smul_sub, smul_inv_smul, h5] at h4
  exact ⟨t, by simpa using Ideal.Quotient.eq.2 h4⟩

theorem exists_splitsCompl (E : Type) [Field E] [NumberField E] (m : ℕ) :
    ∃ p : ℕ, p.Prime ∧ m < p ∧ Formalism.MainNotions.S.SplitsCompl E p := by
  let N : Type := IntermediateField.normalClosure ℚ E (AlgebraicClosure E)
  haveI : NumberField N := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  haveI : IsAlgClosure ℚ (AlgebraicClosure E) := IsAlgClosure.ofAlgebraic ℚ E (AlgebraicClosure E)
  haveI : Normal ℚ N := normalClosure.normal ℚ E (AlgebraicClosure E)
  haveI : IsGalois ℚ N := IsGalois.mk
  obtain ⟨P, hP, hm, hs⟩ := exists_degree_one_avoiding N ((m.factorial : ℤ) * discr E)
    (mul_ne_zero (by exact_mod_cast m.factorial_ne_zero) (discr_ne_zero E))
  have hp := GlobalTheory.SW.SplitPrime.absNorm_prime P hP hs
  have hnd : ¬ ((Ideal.absNorm P : ℕ) : ℤ) ∣ (m.factorial : ℤ) * discr E := by
    rintro ⟨c, hc⟩
    apply hm
    rw [hc]
    push_cast
    exact P.mul_mem_right _ (Ideal.absNorm_mem P)
  refine ⟨_, hp, ?_, fun P' hP' hmem => ⟨?_, ?_⟩⟩
  · by_contra h
    exact hnd (Dvd.dvd.mul_right (by exact_mod_cast Nat.dvd_factorial hp.pos (not_lt.1 h)) _)
  · obtain ⟨Q, hQ, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 N) P'
    have hQm : ((Ideal.absNorm P : ℕ) : 𝓞 N) ∈ Q := by
      have := (Ideal.mem_of_liesOver Q P' _).1 hmem
      simpa using this
    have hsQ := surjective_of_conj hp P Q (Ideal.absNorm_mem P) hQm hs
    have hs' : Function.Surjective (Int.castRingHom (𝓞 E ⧸ P')) := by
      intro x
      obtain ⟨t, ht⟩ := hsQ (algebraMap (𝓞 E ⧸ P') (𝓞 N ⧸ Q) x)
      refine ⟨t, FaithfulSMul.algebraMap_injective (𝓞 E ⧸ P') (𝓞 N ⧸ Q) ?_⟩
      rw [← ht]; simp
    have hq := GlobalTheory.SW.SplitPrime.absNorm_prime P' hP' hs'
    by_contra hne
    have hco : IsCoprime ((Ideal.absNorm P' : ℕ) : 𝓞 E) ((Ideal.absNorm P : ℕ) : 𝓞 E) :=
      ((Nat.coprime_primes hq hp).2 hne).cast
    obtain ⟨a, b, hab⟩ := hco
    exact hP'.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ P'.add_mem (P'.mul_mem_left _ (Ideal.absNorm_mem P')) (P'.mul_mem_left _ hmem)))
  · exact GlobalTheory.Mem.RaySplit.not_mem_sq hp hmem
      ((GlobalTheory.Mem.RaySplit.not_dvd_discr_iff_ramificationIdx E hp).1 (fun h => hnd (h.mul_left _)) P'
        hP'.isPrime hmem)

end GlobalTheory.LargeSplitPrime
