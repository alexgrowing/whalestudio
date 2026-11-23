import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host Formalism.FrobeniusOrbits
open scoped Pointwise

namespace GlobalTheory.PlaceOverPair

theorem under_smul_of_fix {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra K E]
    (σ : E ≃ₐ[ℚ] E) (h : ∀ x : K, σ (algebraMap K E x) = algebraMap K E x) (I : Ideal (𝓞 E)) :
    (σ • I).under (𝓞 K) = I.under (𝓞 K) := by
  ext x
  rw [Ideal.under_def, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have : σ⁻¹ • algebraMap (𝓞 K) (𝓞 E) x = algebraMap (𝓞 K) (𝓞 E) x := by
    rw [inv_smul_eq_iff]
    apply Subtype.val_injective
    exact (h x).symm
  rw [this]

theorem exists_over {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra K E]
    (v : HeightOneSpectrum (𝓞 K)) : ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 K) = v := by
  haveI := v.isMaximal
  obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩

theorem exists_smul_eq {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] {p : ℕ} (hp : p.Prime)
    (P Q : Ideal (𝓞 E)) [P.IsPrime] [Q.IsPrime] (hP : (p : 𝓞 E) ∈ P) (hQ : (p : 𝓞 E) ∈ Q) :
    ∃ σ : E ≃ₐ[ℚ] E, σ • P = Q := by
  have hm : (Ideal.span {(p : ℤ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2
      (Nat.prime_iff_prime_int.1 hp)) (by simpa using hp.ne_zero)
  have key : ∀ (I : Ideal (𝓞 E)) [I.IsPrime], (p : 𝓞 E) ∈ I → I.LiesOver (Ideal.span {(p : ℤ)}) := by
    intro I _ hI
    refine ⟨hm.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
    simpa using hI
  haveI := key P hP
  haveI := key Q hQ
  exact Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P Q (E ≃ₐ[ℚ] E)

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

theorem sqrt_sq : H.sqrtMinusD ^ 2 = -(H.d : H.E) := H.sqd_sq

theorem conj_sqrt : H.conj H.sqrtMinusD = -H.sqrtMinusD := by
  apply H.φ₀.injective
  have h2 := H.conjE_apply H.φ₀ H.sqrtMinusD
  refine h2.trans ?_
  have h3 : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
  rw [map_neg, h3]
  simp

theorem fix_of_sqrt (σ : H.E ≃ₐ[ℚ] H.E) (h : σ H.sqrtMinusD = H.sqrtMinusD) (x : H.K) :
    σ (algebraMap H.K H.E x) = algebraMap H.K H.E x := by
  have : H.K ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
    apply IntermediateField.adjoin_simple_le_iff.2
    rw [IntermediateField.mem_fixedField_iff]
    intro f hf
    have : Subgroup.zpowers σ ≤ MulAction.stabilizer _ H.sqrtMinusD := by
      rw [Subgroup.zpowers_le]
      exact h
    exact this hf
  exact (IntermediateField.mem_fixedField_iff _ _).1 (this x.2) σ (Subgroup.mem_zpowers σ)

theorem exists_over_both {p : ℕ} (hp : p.Prime) (𝔭 : HeightOneSpectrum (𝓞 H.K)) (h𝔭 : (p : 𝓞 H.K) ∈ 𝔭.asIdeal)
    (v : HeightOneSpectrum (𝓞 H.F)) (hv : (p : 𝓞 H.F) ∈ v.asIdeal) :
    ∃ w : HeightOneSpectrum (𝓞 H.E), w.under (𝓞 H.F) = v ∧ w.under (𝓞 H.K) = 𝔭 := by
  haveI := H.hostE_isGalois
  obtain ⟨w, rfl⟩ := exists_over (E := H.E) v
  obtain ⟨u, rfl⟩ := exists_over (E := H.E) 𝔭
  have hu : (p : 𝓞 H.E) ∈ u.asIdeal := by
    have : algebraMap (𝓞 H.K) (𝓞 H.E) (p : 𝓞 H.K) ∈ u.asIdeal := h𝔭
    rwa [map_natCast] at this
  have hw : (p : 𝓞 H.E) ∈ w.asIdeal := by
    have : algebraMap (𝓞 H.F) (𝓞 H.E) (p : 𝓞 H.F) ∈ w.asIdeal := hv
    rwa [map_natCast] at this
  haveI := u.isPrime
  haveI := w.isPrime
  obtain ⟨σ, hσ⟩ := exists_smul_eq hp u.asIdeal w.asIdeal hu hw
  have hs : σ H.sqrtMinusD = H.sqrtMinusD ∨ σ H.sqrtMinusD = -H.sqrtMinusD := by
    apply sq_eq_sq_iff_eq_or_eq_neg.1
    rw [← map_pow, sqrt_sq, map_neg, map_natCast]
  rcases hs with hs | hs
  · refine ⟨w, rfl, HeightOneSpectrum.ext ?_⟩
    show w.asIdeal.under _ = u.asIdeal.under _
    rw [← hσ]
    exact under_smul_of_fix σ (fix_of_sqrt H σ hs) _
  · have hne : H.conj • w.asIdeal ≠ ⊥ := by
      intro h
      apply w.ne_bot
      rw [← inv_smul_smul H.conj w.asIdeal, h, Ideal.smul_bot]
    refine ⟨⟨H.conj • w.asIdeal, inferInstance, hne⟩, HeightOneSpectrum.ext ?_, HeightOneSpectrum.ext ?_⟩
    · exact under_smul_of_fix H.conj (fun x => (H.conjE_mem_hostF_iff _).1 x.2) _
    · show (H.conj • w.asIdeal).under _ = u.asIdeal.under _
      rw [← hσ, smul_smul]
      refine under_smul_of_fix _ (fix_of_sqrt H _ ?_) _
      rw [AlgEquiv.mul_apply, hs, map_neg, conj_sqrt, neg_neg]

end GlobalTheory.PlaceOverPair
