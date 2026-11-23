import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Sd

namespace UpperTheory

section

variable {k : Type} [NormedField k] [IsUltrametricDist k] {K : Type} [Field K]

private theorem norm_ringHom_integer_le_one (σ : K →+* k) (x : 𝓞 K) : ‖σ (x : K)‖ ≤ 1 := by
  have hy : IsIntegral ℤ (σ (x : K)) := map_isIntegral_int σ (RingOfIntegers.isIntegral_coe x)
  have h : IsIntegral (NormedField.valuation (K := k)).integer (σ (x : K)) := hy.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := k))).mem_of_integral h
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h2
  exact_mod_cast h2

private def embeddingPrimeIdeal (σ : K →+* k) : Ideal (𝓞 K) where
  carrier := {x | ‖σ (x : K)‖ < 1}
  add_mem' := by
    intro x y hx hy
    change ‖σ (algebraMap (𝓞 K) K (x + y))‖ < 1
    rw [map_add, map_add]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx hy)
  zero_mem' := by
    change ‖σ (algebraMap (𝓞 K) K 0)‖ < 1
    simp
  smul_mem' := by
    intro c x hx
    change ‖σ (algebraMap (𝓞 K) K (c * x))‖ < 1
    rw [map_mul, map_mul, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (norm_ringHom_integer_le_one σ c)) hx

private theorem norm_embedding_eq_one_of_not_mem (σ : K →+* k) (x : 𝓞 K) (hx : x ∉ embeddingPrimeIdeal σ) :
    ‖σ (algebraMap (𝓞 K) K x)‖ = 1 :=
  le_antisymm (norm_ringHom_integer_le_one σ x) (not_lt.1 hx)

private theorem embedding_ideal_prime (σ : K →+* k) : (embeddingPrimeIdeal σ).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro h
    have h1 : ‖σ (algebraMap (𝓞 K) K 1)‖ < 1 := (Ideal.eq_top_iff_one _).1 h
    simp at h1
  · intro x y hxy
    by_contra hc
    push Not at hc
    change ‖σ (algebraMap (𝓞 K) K (x * y))‖ < 1 at hxy
    rw [map_mul, map_mul, norm_mul, norm_embedding_eq_one_of_not_mem σ x hc.1, norm_embedding_eq_one_of_not_mem σ y hc.2, one_mul] at hxy
    exact lt_irrefl _ hxy

private theorem exists_embedding_prime_above [NumberField K] [CharZero k] [IsAlgClosed k] {l : ℕ} (hp : l.Prime) (hk : ‖(l : k)‖ < 1)
    (w : HeightOneSpectrum (𝓞 K)) (hl : (l : 𝓞 K) ∈ w.asIdeal) :
    ∃ σ : K →+* k, embeddingPrimeIdeal σ = w.asIdeal := by
  classical
  by_contra hne
  push Not at hne
  have σ0 : K →ₐ[ℚ] k := IsAlgClosed.lift
  have hnot : ¬ ((w.asIdeal : Set (𝓞 K)) ⊆ ⋃ σ ∈ ((Finset.univ : Finset (K →ₐ[ℚ] k)) : Set (K →ₐ[ℚ] k)),
      (embeddingPrimeIdeal (σ : K →+* k) : Set (𝓞 K))) := by
    rw [Ideal.subset_union_prime σ0 σ0 (fun σ _ _ _ => embedding_ideal_prime _)]
    rintro ⟨σ, -, hle⟩
    exact hne σ (((w.isPrime.isMaximal w.ne_bot).eq_of_le (embedding_ideal_prime _).ne_top hle).symm)
  obtain ⟨a, haw, ha⟩ := Set.not_subset.1 hnot
  have h1 : ∀ σ : K →ₐ[ℚ] k, ‖σ (a : K)‖ = 1 := by
    intro σ
    refine norm_embedding_eq_one_of_not_mem (σ : K →+* k) a fun h => ha ?_
    simp only [Set.mem_iUnion]
    exact ⟨σ, by simp, h⟩
  have hprod : ‖algebraMap ℚ k (Algebra.norm ℚ (a : K))‖ = 1 := by
    rw [Algebra.norm_eq_prod_embeddings, norm_prod]
    exact Finset.prod_eq_one (fun σ _ => h1 σ)
  have hmem : ((Ideal.absNorm (Ideal.span {a}) : ℕ) : 𝓞 K) ∈ w.asIdeal :=
    (Ideal.span_le.2 (Set.singleton_subset_iff.2 haw)) (Ideal.absNorm_mem _)
  have hdvd : l ∣ Ideal.absNorm (Ideal.span {a}) := by
    by_contra hnd
    have hc : IsCoprime (l : 𝓞 K) ((Ideal.absNorm (Ideal.span {a}) : ℕ) : 𝓞 K) :=
      Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
    obtain ⟨u, v, huv⟩ := hc
    refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    rw [← huv]
    exact add_mem (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hmem)
  have hn : ‖((Ideal.absNorm (Ideal.span {a}) : ℕ) : k)‖ = 1 := by
    rw [Ideal.absNorm_span_singleton, ← hprod, ← Algebra.coe_norm_int, eq_ratCast, Rat.cast_intCast,
      Nat.cast_natAbs]
    rcases abs_choice (Algebra.norm ℤ a) with h | h
    · rw [h]
    · rw [h, Int.cast_neg, norm_neg]
  obtain ⟨m, hm⟩ := hdvd
  rw [hm, Nat.cast_mul, norm_mul] at hn
  have hk1 : ‖(m : k)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ m
  have h2 : ‖(l : k)‖ * ‖(m : k)‖ ≤ ‖(l : k)‖ * 1 := mul_le_mul_of_nonneg_left hk1 (norm_nonneg _)
  linarith

end

theorem exists_ringHom_to_localField_inducing_place : UpperTheory.V.Sd.S2.EmbEx := by
  intro F _ _ _ l hl ι
  refine ⟨fun w hw => ?_, fun w w' τ τ' h h' e => ?_⟩
  · have hk : ‖(l : Qbar l)‖ < 1 := by
      have : (l : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := (map_natCast _ l).symm
      rw [this, norm_algebraMap']
      exact Padic.norm_p_lt_one
    obtain ⟨σ, hσ⟩ := exists_embedding_prime_above hl.out hk w hw
    exact ⟨σ, fun x => by rw [← hσ]; rfl⟩
  · have e2 : ι.toRingHom.comp τ = ι.toRingHom.comp τ' := by
      rcases InfinitePlace.mk_eq_iff.1 e with e | e
      · exact e
      · rw [← e]
        exact (ComplexEmbedding.isReal_iff.1 (IsTotallyReal.complexEmbedding_isReal _)).symm
    have e3 : τ = τ' := RingHom.ext fun x => ι.injective (RingHom.congr_fun e2 x)
    subst e3
    exact HeightOneSpectrum.ext (Ideal.ext fun x => (h x).trans (h' x).symm)

end UpperTheory
