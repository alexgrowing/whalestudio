import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdealCharacterLContinuationNeZeroOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotForallExistsTwoLiesOverAbsNormEqStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NcardPrimesOverEqFinrankOfTrivialFrobeniusStatement
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

namespace GlobalTheory.NormChar

theorem split_trivial (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ P ∈ v.asIdeal.primesOver (𝓞 M), ∀ x : 𝓞 M,
      x ^ Ideal.absNorm v.asIdeal - x ∈ P) : Module.finrank K M = 1 := by
  by_contra h1
  have h2 : 1 < Module.finrank K M := by have := Module.finrank_pos (R := K) (M := M); omega
  obtain ⟨T, hT, hc⟩ := GlobalTheory.T.ncard_primesOver_eq_finrank_of_trivial_frobenius K M
  refine GlobalTheory.T.not_forall_exists_two_degree_one_primes_over K M (S ∪ T) (hS.union hT) fun v hv => ?_
  simp only [Set.mem_union, not_or] at hv
  obtain ⟨hn, hN⟩ := hc v hv.2 (h v hv.1)
  rw [← hn] at h2
  have := v.isMaximal
  obtain ⟨P, P', hP, hP', hne⟩ := (Set.one_lt_ncard_iff (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 M))).1 h2
  have := hP.2
  have := hP'.2
  exact ⟨⟨P, hP.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, ⟨P', hP'.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P'⟩,
    fun e => hne (congrArg HeightOneSpectrum.asIdeal e), hP.2, hP'.2, hN P hP, hN P' hP'⟩

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in

theorem _root_.GlobalTheory.NormChar.smulComm (K L : Type) [Field K] [Field L] [Algebra K L] :
    SMulCommClass (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) := by
  refine ⟨fun σ a x => ?_⟩
  apply RingOfIntegers.ext
  have h1 : ((a • x : 𝓞 L) : L) = algebraMap K L a * x := by
    rw [Algebra.smul_def]; rfl
  have h3 : ((σ • (a • x) : 𝓞 L) : L) = σ ((a • x : 𝓞 L) : L) := rfl
  rw [h3, h1, Algebra.smul_def]
  push_cast
  rw [map_mul, AlgEquiv.commutes]
  rfl

attribute [local instance] smulComm

theorem eq_top_of_frob (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (H : Subgroup (L ≃ₐ[K] L)) [H.Normal] (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ Q : Ideal (𝓞 L), Q.IsPrime → Q.LiesOver v.asIdeal →
      ∀ σ : L ≃ₐ[K] L, IsArithFrobAt (𝓞 K) σ Q → σ ∈ H) : H = ⊤ := by
  set M := IntermediateField.fixedField H with hM
  have : IsGalois K M := IsGalois.of_fixedField_normal_subgroup H
  have h1 : Module.finrank K M = 1 := by
    refine split_trivial K M S hS fun v hv P hP x => ?_
    have := hP.1
    have := hP.2
    obtain ⟨Q, hQ, hQ'⟩ := (inferInstance : Nonempty (P.primesOver (𝓞 L)))
    have hQv : Q.LiesOver v.asIdeal := Ideal.LiesOver.trans Q P v.asIdeal
    have hne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
    have : Finite (𝓞 L ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
    obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 K) (L ≃ₐ[K] L) Q
    have hH := h v hv Q hQ hQv σ hσ
    have h5 : Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) = Ideal.absNorm v.asIdeal := by
      rw [← hQv.over, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have h6 := hσ (algebraMap (𝓞 M) (𝓞 L) x)
    rw [h5] at h6
    have h7 : (MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L) σ) (algebraMap (𝓞 M) (𝓞 L) x) = algebraMap (𝓞 M) (𝓞 L) x := by
      apply RingOfIntegers.ext
      exact (x : M).2 ⟨σ, hH⟩
    rw [h7] at h6
    rw [hQ'.over, Ideal.mem_comap, map_sub, map_pow, ← neg_mem_iff, neg_sub]
    exact h6
  have h2 : M = ⊥ := IntermediateField.finrank_eq_one_iff.1 h1
  rw [← IntermediateField.fixingSubgroup_fixedField H, ← hM, h2, IntermediateField.fixingSubgroup_bot]

theorem exists_prime_norm_char_ne_one : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ), m.Prime → Irreducible (cyclotomic m K) → ∀ χ : (ZMod m)ˣ →* ℂˣ, χ ≠ 1 → ∃ (P : HeightOneSpectrum (𝓞 K)) (u : (ZMod m)ˣ), (u : ZMod m) = (Ideal.absNorm P.asIdeal : ℕ) ∧ χ u ≠ 1 := by
  intro K _ _ m hm hirr χ hχ
  by_contra hcon
  push Not at hcon
  have : NeZero m := ⟨hm.ne_zero⟩
  let L := CyclotomicField m K
  have : IsGalois K L := IsCyclotomicExtension.isGalois {m} K L
  let e := IsCyclotomicExtension.autEquivPow L hirr
  have hz := IsCyclotomicExtension.zeta_spec m K L
  have hm0 : Ideal.span {(m : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hm.ne_zero
  have hH := eq_top_of_frob K L (χ.comp e.toMonoidHom).ker {v | v.asIdeal ∣ Ideal.span {(m : 𝓞 K)}}
    (Ideal.finite_factors hm0) (fun v hv Q hQ hQv σ hσ => by
      have hζ := hz.toInteger_isPrimitiveRoot
      have hmQ : (m : 𝓞 L) ∉ Q := by
        intro hmQ
        apply hv
        rw [Set.mem_ofPred_eq, Ideal.dvd_span_singleton, hQv.over, Ideal.mem_comap, map_natCast]
        exact hmQ
      have h3 := AlgHom.IsArithFrobAt.apply_of_pow_eq_one hσ hζ.pow_eq_one hmQ
      have h5 : Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) = Ideal.absNorm v.asIdeal := by
        rw [← hQv.over, Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rw [h5] at h3
      have h4 : σ (IsCyclotomicExtension.zeta m K L) =
          IsCyclotomicExtension.zeta m K L ^ Ideal.absNorm v.asIdeal := by
        have := congrArg (fun y : 𝓞 L => (y : L)) h3
        exact this
      have h6 := hz.autToPow_spec K σ
      rw [h4] at h6
      have h7 : ((hz.autToPow K σ : (ZMod m)ˣ) : ZMod m).val ≡ Ideal.absNorm v.asIdeal [MOD m] := by
        have := (hz.isOfFinOrder hm.ne_zero).pow_eq_pow_iff_modEq.1 h6
        rwa [← hz.eq_orderOf] at this
      refine hcon v (e σ) ?_
      rw [← (ZMod.natCast_eq_natCast_iff _ _ _).2 h7, ZMod.natCast_zmod_val]
      rfl)
  apply hχ
  ext1 u
  have : e.symm u ∈ (χ.comp e.toMonoidHom).ker := hH ▸ Subgroup.mem_top _
  simpa using this

end GlobalTheory.NormChar
