import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open scoped Pointwise

namespace GlobalTheory.Mem.Chr

section General

variable {L : Type} [Field L] [NumberField L]

theorem liesOver_span_of_natCast_mem {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 L)) [P.IsPrime] (h : ((p : ℕ) : 𝓞 L) ∈ P) :
    P.LiesOver (Ideal.span {(p : ℤ)}) := by
  have : Fact p.Prime := ⟨hp⟩
  have hm : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  refine ⟨hm.eq_of_le (Ideal.IsPrime.under ℤ P).ne_top ?_⟩
  rw [Ideal.span_le, Set.singleton_subset_iff]
  show algebraMap ℤ (𝓞 L) (p : ℤ) ∈ P
  simpa using h

theorem ncard_places_eq_primesOver {p : ℕ} (hp : p.Prime) :
    {v : HeightOneSpectrum (𝓞 L) | ((p : ℕ) : 𝓞 L) ∈ v.asIdeal}.ncard =
      ((Ideal.span {(p : ℤ)}).primesOver (𝓞 L)).ncard := by
  rw [← Set.ncard_image_of_injective _ (fun v w h => HeightOneSpectrum.ext h :
    Function.Injective (HeightOneSpectrum.asIdeal (R := 𝓞 L)))]
  congr 1
  ext P
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.isPrime, liesOver_span_of_natCast_mem hp _ hv⟩
  · rintro ⟨h1, h2⟩
    have hm : ((p : ℕ) : 𝓞 L) ∈ P := by
      have : (p : ℤ) ∈ P.under ℤ := by rw [← h2.over]; exact Ideal.mem_span_singleton_self _
      simpa using (show algebraMap ℤ (𝓞 L) (p : ℤ) ∈ P from this)
    refine ⟨⟨P, h1, ?_⟩, hm, rfl⟩
    rintro rfl
    exact hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hm))

theorem splitsC_place [IsGalois ℚ L] {p : ℕ} (hp : p.Prime) (hs : SplitsC L p) (v : HeightOneSpectrum (𝓞 L))
    (hv : ((p : ℕ) : 𝓞 L) ∈ v.asIdeal) :
    Ideal.absNorm v.asIdeal = p ∧ ((p : ℕ) : 𝓞 L) ∉ v.asIdeal ^ 2 ∧
      ∀ σ : L ≃ₐ[ℚ] L, σ • v.asIdeal = v.asIdeal → σ = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have := v.isPrime
  have := liesOver_span_of_natCast_mem hp _ hv
  have hm : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have h0 : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by simpa using hp.ne_zero
  have h1 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 L) (L ≃ₐ[ℚ] L)
  unfold SplitsC at hs
  rw [← ncard_places_eq_primesOver hp, hs, IsGalois.card_aut_eq_finrank] at h1
  have h2 : (Ideal.span {(p : ℤ)}).ramificationIdxIn (𝓞 L) * (Ideal.span {(p : ℤ)}).inertiaDegIn (𝓞 L) = 1 :=
    (mul_eq_left₀ Module.finrank_pos.ne').1 h1
  have h3 := Ideal.card_stabilizer_eq (G := L ≃ₐ[ℚ] L) (Ideal.span {(p : ℤ)}) v.asIdeal
  rw [h2] at h3
  have he := Nat.eq_one_of_mul_eq_one_right h2
  have hf := Nat.eq_one_of_mul_eq_one_left h2
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ v.asIdeal (L ≃ₐ[ℚ] L),
    ← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) v.asIdeal h0] at he
  rw [Ideal.inertiaDegIn_eq_inertiaDeg _ v.asIdeal (L ≃ₐ[ℚ] L)] at hf
  refine ⟨?_, ?_, ?_⟩
  · rw [← Ideal.pow_inertiaDeg p v.asIdeal, hf, pow_one]
  · intro h
    refine (Ideal.ramificationIdx'_ne_one_iff ?_).2 ?_ he
    · simpa [Ideal.map_span] using hv
    · simpa [Ideal.map_span] using h
  · intro σ hσ
    have : (MulAction.stabilizer (L ≃ₐ[ℚ] L) v.asIdeal) = ⊥ := Subgroup.card_eq_one.1 h3
    exact Subgroup.mem_bot.1 (this ▸ hσ)

theorem conjPl_iff_smul (σ : L ≃ₐ[ℚ] L) (v v' : HeightOneSpectrum (𝓞 L)) :
    ConjPl σ.toRingEquiv v v' ↔ σ • v.asIdeal = v'.asIdeal := by
  rw [conjPl_iff_mem]
  constructor
  · intro h
    ext y
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    exact h _ _ (σ.apply_symm_apply (y : L)).symm
  · intro h x y hxy
    have e : y = σ • x := RingOfIntegers.ext hxy
    rw [e, ← h, Ideal.smul_mem_pointwise_smul_iff]

theorem under_smul_of_fix (b : L) (σ : L ≃ₐ[ℚ] L) (h : σ b = b) (P : Ideal (𝓞 L)) :
    (σ • P).under (𝓞 (IntermediateField.adjoin ℚ {b})) = P.under (𝓞 (IntermediateField.adjoin ℚ {b})) := by
  have hfix : ∀ x ∈ IntermediateField.adjoin ℚ {b}, σ x = x := by
    intro x hx
    have : IntermediateField.adjoin ℚ {b} ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
      rw [IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]
      rintro _ hτ
      have : Subgroup.zpowers σ ≤ MulAction.stabilizer _ b := (Subgroup.zpowers_le).2 h
      exact this hτ
    exact (IntermediateField.mem_fixedField_iff _ _).1 (this hx) σ (Subgroup.mem_zpowers σ)
  ext a
  have e : σ • algebraMap _ (𝓞 L) a = algebraMap _ (𝓞 L) a := RingOfIntegers.ext (hfix _ (a : IntermediateField.adjoin ℚ {b}).2)
  rw [Ideal.mem_under, Ideal.mem_under]
  conv_lhs => rw [← e]
  rw [Ideal.smul_mem_pointwise_smul_iff]

theorem exists_smul_fix_of_under_eq [IsGalois ℚ L] (b : L) (P P' : Ideal (𝓞 L)) [P.IsPrime] [P'.IsPrime]
    (h : P.under (𝓞 (IntermediateField.adjoin ℚ {b})) = P'.under (𝓞 (IntermediateField.adjoin ℚ {b}))) :
    ∃ σ : L ≃ₐ[ℚ] L, σ b = b ∧ σ • P = P' := by
  set K := IntermediateField.adjoin ℚ {b} with hK
  have : P'.LiesOver (P.under (𝓞 K)) := ⟨h⟩
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (P.under (𝓞 K)) P P' (L ≃ₐ[K] L)
  refine ⟨τ.restrictScalars ℚ, τ.commutes (⟨b, IntermediateField.mem_adjoin_simple_self ℚ b⟩ : K), ?_⟩
  rw [← hτ]
  ext y
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem under_eq_iff_under_ne [IsGalois ℚ L] {p : ℕ} (hp : p.Prime) (hs : SplitsC L p) (b : L) (hb0 : b ≠ 0)
    (hb : ∀ σ : L ≃ₐ[ℚ] L, σ b = b ∨ σ b = -b) (c : L ≃ₐ[ℚ] L) (hc : c b = -b)
    (v v' : HeightOneSpectrum (𝓞 L)) (hv : ((p : ℕ) : 𝓞 L) ∈ v.asIdeal) (hvv : c • v.asIdeal = v'.asIdeal)
    (Q : HeightOneSpectrum (𝓞 (IntermediateField.adjoin ℚ {b})))
    (hQ : ((p : ℕ) : 𝓞 (IntermediateField.adjoin ℚ {b})) ∈ Q.asIdeal) :
    v.under (𝓞 (IntermediateField.adjoin ℚ {b})) = Q ↔ v'.under (𝓞 (IntermediateField.adjoin ℚ {b})) ≠ Q := by
  have := v.isPrime
  have := v'.isPrime
  constructor
  · rintro rfl h
    obtain ⟨σ, hσb, hσ⟩ := exists_smul_fix_of_under_eq b v.asIdeal v'.asIdeal
      (congrArg HeightOneSpectrum.asIdeal h).symm
    have h1 : σ⁻¹ * c = 1 := (splitsC_place hp hs v hv).2.2 _ (by rw [mul_smul, hvv, ← hσ, inv_smul_smul])
    rw [inv_mul_eq_one] at h1
    rw [h1, hc] at hσb
    exact hb0 (by linear_combination (-1 / 2 : L) * hσb)
  · intro h
    have := Q.isPrime
    obtain ⟨⟨W, hW, hWQ⟩⟩ := (inferInstance : Nonempty (Q.asIdeal.primesOver (𝓞 L)))
    have hpW : ((p : ℕ) : 𝓞 L) ∈ W := by
      rw [hWQ.over, Ideal.mem_under] at hQ
      simpa using hQ
    have := liesOver_span_of_natCast_mem hp _ hv
    have := liesOver_span_of_natCast_mem hp _ hpW
    obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) v.asIdeal W (L ≃ₐ[ℚ] L)
    rcases hb σ with h1 | h1
    · apply HeightOneSpectrum.ext
      rw [hWQ.over, ← hσ, under_smul_of_fix b σ h1]
      rfl
    · exfalso
      apply h
      apply HeightOneSpectrum.ext
      have h2 : (σ * c⁻¹) b = b := by
        have : c⁻¹ b = -b := by
          have h3 : c⁻¹ (c b) = b := c.symm_apply_apply b
          rw [hc, map_neg] at h3
          exact neg_eq_iff_eq_neg.1 h3
        rw [AlgEquiv.mul_apply, this, map_neg, h1, neg_neg]
      have h4 : (σ * c⁻¹) • v'.asIdeal = W := by rw [← hvv, mul_smul, inv_smul_smul, hσ]
      rw [hWQ.over, ← h4, under_smul_of_fix b _ h2]
      rfl

end General

open Classical in

theorem splitsC_main : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (p : ℕ), p.Prime → SplitsC H.E p → ∀ v : HeightOneSpectrum (𝓞 H.E), OverP H p v → Ideal.absNorm v.asIdeal = p ∧ ((p : ℕ) : 𝓞 H.E) ∉ v.asIdeal ^ 2 ∧ IsSplitPl H v ∧ ∀ (Q : HeightOneSpectrum (𝓞 H.K)), ((p : ℕ) : 𝓞 H.K) ∈ Q.asIdeal → ∀ v', ConjPl H.conj.toRingEquiv v v' → OverP H p v' ∧ (v.under (𝓞 H.K) = Q ↔ v'.under (𝓞 H.K) ≠ Q) := by
  intro R H p hp hs v hv
  have hG : IsGalois ℚ H.E := H.hostE_isGalois
  have hsq := H.sqrtMinusD_sq
  have hc := H.conj_sqrtMinusD
  have hb0 : H.sqrtMinusD ≠ 0 := by
    intro h
    rw [h] at hsq
    have : (H.d : H.E) = 0 := by linear_combination hsq
    have h1 : H.d = 0 := by exact_mod_cast this
    have := H.qd_big.2
    omega
  have hb : ∀ σ : H.E ≃ₐ[ℚ] H.E, σ H.sqrtMinusD = H.sqrtMinusD ∨ σ H.sqrtMinusD = -H.sqrtMinusD := by
    intro σ
    apply sq_eq_sq_iff_eq_or_eq_neg.1
    rw [← map_pow, hsq, map_neg, map_natCast]
  obtain ⟨h1, h2, h3⟩ := splitsC_place hp hs v hv
  refine ⟨h1, h2, ?_, fun Q hQ v' hvv => ⟨?_, ?_⟩⟩
  · by_contra hn
    unfold IsSplitPl at hn
    push Not at hn
    have hle : H.conj • v.asIdeal ≤ v.asIdeal := by
      intro y hy
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
      obtain ⟨z, hz, hzv⟩ := hn _ hy
      have e : z = y := RingOfIntegers.ext (hz.trans (H.conj.apply_symm_apply (y : H.E)))
      exact e ▸ hzv
    obtain ⟨w, hw, -⟩ := existsUnique_conjPl H.conj.toRingEquiv v
    have hw' := (conjPl_iff_smul H.conj v w).1 hw
    have heq : H.conj • v.asIdeal = v.asIdeal := by
      rw [hw'] at hle ⊢
      exact w.isMaximal.eq_of_le v.isPrime.ne_top hle
    rw [h3 _ heq] at hc
    have hc' : H.sqrtMinusD = -H.sqrtMinusD := hc
    exact hb0 (by linear_combination (1 / 2 : H.E) * hc')
  · exact ((conjPl_iff_mem _ v v').1 hvv _ _ (by simp)).1 hv
  · exact under_eq_iff_under_ne hp hs H.sqrtMinusD hb0 hb H.conj hc v v' hv ((conjPl_iff_smul H.conj v v').1 hvv) Q hQ

end GlobalTheory.Mem.Chr
