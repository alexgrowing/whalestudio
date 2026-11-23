import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.Mem.Chr (unitIdl)

namespace UpperTheory.V.Af.Tw

private theorem loc (K : Type) [Field K] [NumberField K] {N : ℕ} (hN : N ≠ 0) (v : HeightOneSpectrum (𝓞 K)) :
    ∃ M : ℕ, 0 < M ∧ ∀ x : v.adicCompletion K, Valued.v x = 1 → ∀ k : ℕ, M ∣ k →
      Valued.v (x ^ k - 1) ≤ Valued.v (N : v.adicCompletion K) := by
  classical
  let I : Ideal (v.adicCompletionIntegers K) := Ideal.span {(N : v.adicCompletionIntegers K)}
  have hI : I ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    intro h
    apply hN
    have := congrArg (fun r : v.adicCompletionIntegers K => (r : v.adicCompletion K)) h
    simpa using this
  haveI := Formalism.UG.P.glint_finite_quotient_of_dvr inferInstance I hI
  haveI : Finite (v.adicCompletionIntegers K ⧸ I)ˣ :=
    Finite.of_injective (fun u : (v.adicCompletionIntegers K ⧸ I)ˣ => (u : v.adicCompletionIntegers K ⧸ I))
      (fun a b h => Units.ext h)
  refine ⟨Nat.card (v.adicCompletionIntegers K ⧸ I)ˣ, Nat.card_pos, ?_⟩
  intro x hx k hk
  have hxR : x ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hx.le
  have hyR : x⁻¹ ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hx, inv_one]
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx
    exact zero_ne_one hx
  let u : (v.adicCompletionIntegers K)ˣ :=
    ⟨⟨x, hxR⟩, ⟨x⁻¹, hyR⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩
  obtain ⟨j, rfl⟩ := hk
  have h1 : (Units.map (Ideal.Quotient.mk I).toMonoidHom u) ^ (Nat.card (v.adicCompletionIntegers K ⧸ I)ˣ * j) = 1 := by
    rw [pow_mul, pow_card_eq_one', one_pow]
  have h2 : ((⟨x, hxR⟩ : v.adicCompletionIntegers K) ^ (Nat.card (v.adicCompletionIntegers K ⧸ I)ˣ * j) - 1) ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, sub_eq_zero]
    have := congrArg Units.val h1
    simpa [u] using this
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h2
  have hy' : x ^ (Nat.card (v.adicCompletionIntegers K ⧸ I)ˣ * j) - 1 =
      (y : v.adicCompletion K) * (N : v.adicCompletion K) := by
    have := congrArg (fun r : v.adicCompletionIntegers K => (r : v.adicCompletion K)) hy
    simpa using this.symm
  rw [hy', map_mul]
  have hyle : Valued.v (y : v.adicCompletion K) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 y.2
  simpa using mul_le_mul' hyle (le_refl (Valued.v (N : v.adicCompletion K)))

theorem levPow : LevPow := by
  unfold LevPow
  intro K _ _ N hN
  choose M hMpos hM using fun v : HeightOneSpectrum (𝓞 K) => loc K hN v
  have hN0 : Ideal.span {(N : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  have hfin := Ideal.finite_factors hN0
  refine ⟨∏ v ∈ hfin.toFinset, M v, Finset.prod_pos (fun v _ => hMpos v), ?_⟩
  intro u hu
  refine ⟨pow_mem hu _, fun v => ?_⟩
  have hpow : ∀ P : ℕ, (u ^ P).val.2 v = (u.val.2 v) ^ P := by
    intro P
    induction P with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ, Units.val_mul, pow_succ, ← ih]
      rfl
  have hu1 : Valued.v (u.val.2 v) = 1 := hu v
  show Valued.v ((u ^ (∏ v ∈ hfin.toFinset, M v)).val.2 v - 1) ≤ Valued.v (N : v.adicCompletion K)
  rw [hpow]
  by_cases hv : v ∈ hfin.toFinset
  · exact hM v _ hu1 _ (Finset.dvd_prod_of_mem M hv)
  · rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton] at hv
    have hlt := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) v (N : 𝓞 K)).not.2 hv
    have hle := HeightOneSpectrum.valuation_le_one (K := K) v (N : 𝓞 K)
    have h2 := PI.IntAdCpctOpenWork.valued_algebraMap v (N : K)
    simp at h2 hlt hle
    have hN1 : Valued.v (N : v.adicCompletion K) = 1 := by
      rw [h2]
      exact le_antisymm hle hlt
    rw [hN1]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
    · rw [map_pow, hu1, one_pow]
    · rw [map_one]

end UpperTheory.V.Af.Tw
