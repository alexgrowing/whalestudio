import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.PlaceConjAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.PlaceHom

open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical nonZeroDivisors

namespace UpperTheory.V.Z.Int

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {E : Type} [Field E] [NumberField E]

private theorem nu_mul (x y : ℂ) : nu ι (x * y) = nu ι x * nu ι y := by
  simp [nu]

private theorem nu_pow (x : ℂ) (n : ℕ) : nu ι (x ^ n) = nu ι x ^ n := by
  simp [nu]

private theorem nu_inv (x : ℂ) : nu ι x⁻¹ = (nu ι x)⁻¹ := by
  simp [nu]

private theorem nu_neg (x : ℂ) : nu ι (-x) = nu ι x := by
  simp [nu]

private theorem nu_nonneg (x : ℂ) : 0 ≤ nu ι x := norm_nonneg _

private theorem nu_pos {x : ℂ} (hx : x ≠ 0) : 0 < nu ι x :=
  norm_pos_iff.2 ((map_ne_zero ι.symm).2 hx)

private theorem nu_prod {α : Type*} (s : Finset α) (f : α → ℂ) :
    nu ι (∏ i ∈ s, f i) = ∏ i ∈ s, nu ι (f i) := by
  simp [nu, map_prod, norm_prod]

private theorem nu_le_one_iff {w : HeightOneSpectrum (𝓞 E)} {τ : E →+* ℂ} (hτ : τ ∈ Ov ι w)
    (a : E) : nu ι (τ a) ≤ 1 ↔ w.valuation E a ≤ 1 := by
  obtain ⟨u, ψ, h1, h2, h3⟩ := placeHom l ι E τ
  obtain rfl := (h3 w).1 hτ
  have h := h2 (algebraMap E _ a)
  have hv : Valued.v (algebraMap E (w.adicCompletion E) a) = w.valuation E a :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w a
  rwa [h1, hv] at h

private theorem nu_eq_one {w : HeightOneSpectrum (𝓞 E)} {τ : E →+* ℂ} (hτ : τ ∈ Ov ι w)
    {a : E} (ha : w.valuation E a = 1) : nu ι (τ a) = 1 := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have h1 := (nu_le_one_iff ι hτ a).2 ha.le
  have h2 := (nu_le_one_iff ι hτ a⁻¹).2 (by rw [map_inv₀, ha, inv_one])
  rw [map_inv₀, nu_inv] at h2
  have hp := nu_pos ι ((map_ne_zero τ).2 ha0)
  exact le_antisymm h1 ((inv_le_one₀ hp).1 h2)

private theorem exists_place (τ : E →+* ℂ) : ∃ u : HeightOneSpectrum (𝓞 E), τ ∈ Ov ι u := by
  obtain ⟨u, _, _, _, h3⟩ := placeHom l ι E τ
  exact ⟨u, (h3 u).2 rfl⟩

private theorem nu_int (τ : E →+* ℂ) (x : 𝓞 E) : nu ι (τ x) ≤ 1 := by
  obtain ⟨u, hu⟩ := exists_place ι τ
  exact (nu_le_one_iff ι hu _).2 (u.valuation_le_one x)

private theorem val_unif (w : HeightOneSpectrum (𝓞 E)) :
    w.valuation E (unif w : E) = WithZero.exp (-1 : ℤ) := by
  have h := unif_spec w
  unfold IsUnifAt at h
  have h' : Valued.v (algebraMap E (w.adicCompletion E) (unif w : E)) = WithZero.exp (-1 : ℤ) := h
  have hv : Valued.v (algebraMap E (w.adicCompletion E) (unif w : E)) = w.valuation E (unif w : E) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  rwa [hv] at h'

private theorem exists_gen (w : HeightOneSpectrum (𝓞 E)) :
    ∃ h : ℕ, h ≠ 0 ∧ ∃ α : 𝓞 E, α ≠ 0 ∧ Ideal.span {α} = w.asIdeal ^ h := by
  let I0 : (Ideal (𝓞 E))⁰ := ⟨w.asIdeal, mem_nonZeroDivisors_of_ne_zero w.ne_bot⟩
  obtain ⟨J, hJ⟩ : ∃ J : (Ideal (𝓞 E))⁰, J = I0 ^ Nat.card (ClassGroup (𝓞 E)) := ⟨_, rfl⟩
  have h1 : ClassGroup.mk0 J = 1 := by
    rw [hJ, map_pow, pow_card_eq_one']
  have h2 : (J : Ideal (𝓞 E)).IsPrincipal := (ClassGroup.mk0_eq_one_iff J.2).1 h1
  have h3 : (J : Ideal (𝓞 E)) = w.asIdeal ^ Nat.card (ClassGroup (𝓞 E)) := by
    rw [hJ]
    rfl
  obtain ⟨⟨α, hα⟩⟩ := h2
  have hα' : Ideal.span {α} = w.asIdeal ^ Nat.card (ClassGroup (𝓞 E)) := by
    rw [← h3, hα]
  refine ⟨_, Nat.card_pos.ne', α, ?_, hα'⟩
  rintro rfl
  rw [Ideal.span_singleton_zero] at hα'
  exact pow_ne_zero _ w.ne_bot hα'.symm

private theorem val_gen (w : HeightOneSpectrum (𝓞 E)) {h : ℕ} {α : 𝓞 E} (h0 : α ≠ 0)
    (hs : Ideal.span {α} = w.asIdeal ^ h) :
    w.valuation E (α : E) = (w.valuation E (unif w : E)) ^ h := by
  have h1 : w.valuation E (α : E) = w.intValuation α := w.valuation_of_algebraMap α
  rw [h1, w.intValuation_eq_exp_neg_multiplicity h0, hs, val_unif, ← WithZero.exp_nsmul]
  have hm : multiplicity w.asIdeal (w.asIdeal ^ h) = h :=
    multiplicity_pow_self w.ne_bot (by simpa using w.isPrime.ne_top) h
  rw [hm]
  simp

private theorem nu_gen_off {w u : HeightOneSpectrum (𝓞 E)} {h : ℕ} {α : 𝓞 E}
    (hs : Ideal.span {α} = w.asIdeal ^ h) (hne : u ≠ w) {τ : E →+* ℂ} (hτ : τ ∈ Ov ι u) :
    nu ι (τ α) = 1 := by
  have hα : α ∉ u.asIdeal := by
    intro hm
    have hle : w.asIdeal ^ h ≤ u.asIdeal := by
      rw [← hs, Ideal.span_singleton_le_iff_mem]
      exact hm
    have hwu : w.asIdeal ≤ u.asIdeal := u.isPrime.le_of_pow_le hle
    exact hne (HeightOneSpectrum.ext (w.isMaximal.eq_of_le u.isPrime.ne_top hwu).symm)
  have hmem := (Finset.mem_filter.1 hτ).2 α
  exact le_antisymm (nu_int ι τ α) (not_lt.1 (fun hlt => hα (hmem.2 hlt)))

private theorem prod_emb (α : 𝓞 E) :
    ∏ τ : E →+* ℂ, τ (α : E) = ((Algebra.norm ℤ α : ℤ) : ℂ) := by
  have h1 := Algebra.norm_eq_prod_embeddings ℚ ℂ (α : E)
  have h2 : ((Algebra.norm ℤ α : ℤ) : ℚ) = Algebra.norm ℚ (α : E) := Algebra.coe_norm_int α
  rw [← h2] at h1
  have h3 : ((Algebra.norm ℤ α : ℤ) : ℂ) = ∏ σ : E →ₐ[ℚ] ℂ, σ (α : E) := by
    rw [← h1]
    simp
  rw [h3]
  exact Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) _ _ (fun τ => rfl)

end SlopeTestRemainingChoices

theorem prodNorm : ProdNorm := by
  intro l _ ι E _ _ w
  have hlt : ∀ τ ∈ Ov ι w, 0 < nu ι (τ (unif w : E)) ∧ nu ι (τ (unif w : E)) < 1 := by
    intro τ hτ
    have hp := nu_pos ι ((map_ne_zero τ).2 (unif w).ne_zero)
    refine ⟨hp, ?_⟩
    have h1 : ¬ w.valuation E (unif w : E)⁻¹ ≤ 1 := by
      rw [map_inv₀, val_unif, not_le, ← WithZero.exp_neg, neg_neg, ← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.2 one_pos
    rw [← nu_le_one_iff ι hτ, map_inv₀, nu_inv, not_le] at h1
    exact (one_lt_inv₀ hp).1 h1
  refine ⟨hlt, ?_⟩
  obtain ⟨h, hh, α, h0, hs⟩ := exists_gen w
  have hon : ∀ τ ∈ Ov ι w, nu ι (τ α) = nu ι (τ (unif w : E)) ^ h := by
    intro τ hτ
    have hv : w.valuation E ((α : E) / (unif w : E) ^ h) = 1 := by
      have hu : w.valuation E (unif w : E) ≠ 0 := by
        rw [val_unif]
        exact WithZero.exp_ne_zero
      rw [map_div₀, map_pow, val_gen w h0 hs, div_self (pow_ne_zero _ hu)]
    have h1 := nu_eq_one ι hτ hv
    have hp := nu_pos ι ((map_ne_zero τ).2 (unif w).ne_zero)
    rw [map_div₀, map_pow, div_eq_mul_inv, nu_mul, nu_inv, nu_pow] at h1
    exact (mul_inv_eq_one₀ (pow_ne_zero _ hp.ne')).1 h1
  have hoff : ∀ τ ∈ (Finset.univ : Finset (E →+* ℂ)), τ ∉ Ov ι w → nu ι (τ α) = 1 := by
    intro τ _ hτ
    obtain ⟨u, hu⟩ := exists_place ι τ
    have hne : u ≠ w := by
      rintro rfl
      exact hτ hu
    exact nu_gen_off ι hs hne hu
  have hall : nu ι ((Algebra.norm ℤ α : ℤ) : ℂ) = (∏ τ ∈ Ov ι w, nu ι (τ (unif w : E))) ^ h := by
    rw [← prod_emb, nu_prod, ← Finset.prod_subset (Finset.subset_univ (Ov ι w)) hoff,
      Finset.prod_congr rfl hon, Finset.prod_pow]
  have hnorm : (Algebra.norm ℤ α).natAbs = normV w ^ h := by
    rw [← Ideal.absNorm_span_singleton, hs, map_pow]
    rfl
  have hN : nu ι ((Algebra.norm ℤ α : ℤ) : ℂ) = nu ι (normV w : ℂ) ^ h := by
    rw [← nu_pow]
    rcases Int.natAbs_eq (Algebra.norm ℤ α) with he | he
    · rw [he, hnorm]
      simp
    · rw [he, hnorm]
      simp [nu_neg]
  have hfin := hall.symm.trans hN
  exact (pow_left_inj₀ (Finset.prod_nonneg fun _ _ => nu_nonneg ι _) (nu_nonneg ι _) hh).1 hfin

end UpperTheory.V.Z.Int
