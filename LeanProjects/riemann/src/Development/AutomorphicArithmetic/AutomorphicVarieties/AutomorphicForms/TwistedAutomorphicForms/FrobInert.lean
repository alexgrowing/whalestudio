import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V.Af UpperTheory.V.Af.Tw
open scoped Pointwise

section SlopeTestRemainingChoices

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra L Ω]
  [Algebra K Ω] [IsScalarTower K L Ω]

omit [NumberField L] in
private theorem int_mem (A : ValuationSubring Ω) (x : 𝓞 L) : algebraMap L Ω (x : L) ∈ A := by
  have hb : IsIntegral ℤ (algebraMap L Ω (x : L)) := x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom
  have h : IsIntegral A (algebraMap L Ω (x : L)) := hb.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [← hy]
  exact y.2

private theorem place_between {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), IsPlaceOver A w ∧ w.asIdeal.LiesOver v.asIdeal := by
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A (int_mem A)
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hu : v.asIdeal = P.under (𝓞 K) := by
    ext x
    rw [← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply K L Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨P, inferInstance, hne⟩, hP, ⟨hu⟩⟩

private theorem normV_under (w : HeightOneSpectrum (𝓞 L)) :
    normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 L) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

omit [NumberField K] in
private theorem frob_val {A : ValuationSubring Ω} {q : ℕ} (hq : q ≠ 0) {σ : G K Ω} (hσ : IsFrob A q σ) {x : Ω}
    (hx : A.valuation x ≤ 1) : A.valuation (σ x) ≤ 1 ∧ (A.valuation x < 1 → A.valuation (σ x) < 1) := by
  have e : σ x = (σ x - x ^ q) + x ^ q := by ring
  have h1 := hσ.2 x hx
  constructor
  · rw [e]
    exact Valuation.map_add_le _ h1.le (by rw [map_pow]; exact pow_le_one₀ zero_le hx)
  · intro h
    rw [e]
    exact Valuation.map_add_lt _ h1 (by rw [map_pow]; exact pow_lt_one₀ zero_le h hq)

omit [NumberField K] in
private theorem frob_sq {A : ValuationSubring Ω} {q : ℕ} (hq : q ≠ 0) {σ : G K Ω} (hσ : IsFrob A q σ) :
    IsFrob A (q ^ 2) (σ * σ) := by
  refine ⟨mul_mem hσ.1 hσ.1, fun x hx => ?_⟩
  have h1 := hσ.2 x hx
  have h2 := (frob_val hq hσ h1.le).2 h1
  have hxq : A.valuation (x ^ q) ≤ 1 := by rw [map_pow]; exact pow_le_one₀ zero_le hx
  have h3 := hσ.2 (x ^ q) hxq
  have e : (σ * σ) x - x ^ q ^ 2 = σ (σ x - x ^ q) + (σ (x ^ q) - (x ^ q) ^ q) := by
    rw [AlgEquiv.mul_apply, map_sub, sq, pow_mul]; ring
  rw [e]
  exact Valuation.map_add_lt _ h2 h3

end SlopeTestRemainingChoices

theorem UpperTheory.V.Af.Tw.frobInert :
    UpperTheory.V.Af.Tw.FrobInert := by
  intro F L Ω _ _ _ _ _ _ _ _ _ _ _ h2 v A hU hA σ hσ hn
  obtain ⟨w, hw, hwv⟩ := place_between (L := L) hA
  have : Algebra.IsQuadraticExtension F L := ⟨h2⟩
  have : IsGalois F L := inferInstance
  have hq : normV v ≠ 0 := (lt_trans zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'
  have hu : w.under (𝓞 F) = v := HeightOneSpectrum.ext hwv.over.symm
  set c : L ≃ₐ[F] L := AlgEquiv.restrictNormalHom L σ with hc
  have hcx : ∀ x : L, algebraMap L Ω (c x) = σ (algebraMap L Ω x) := fun x =>
    AlgEquiv.restrictNormal_commutes σ L x
  have hc1 : c ≠ 1 := fun h => hn ⟨{ σ with
    commutes' := fun x => by
      have := hcx x
      rw [h] at this
      exact this.symm }, rfl⟩
  have := w.isMaximal
  have hcw : c • w.asIdeal = w.asIdeal := by
    have hmax : (c • w.asIdeal).IsMaximal := by
      exact Ideal.map_isMaximal_of_equiv (MulSemiringAction.toRingEquiv _ _ c)
    refine hmax.eq_of_le w.isPrime.ne_top ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 hy |> fun h => (⟨c⁻¹ • y, h, smul_inv_smul c y⟩ : ∃ x ∈ w.asIdeal, c • x = y)
    rw [← hw] at hx ⊢
    have e : algebraMap L Ω ((c • x : 𝓞 L) : L) = σ (algebraMap L Ω (x : L)) := hcx x
    rw [e]
    exact (frob_val hq hσ hx.le).2 hx
  have huniq : ∀ P : Ideal (𝓞 L), P.IsPrime → P.LiesOver v.asIdeal → P = w.asIdeal := by
    intro P _ _
    obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal w.asIdeal P (L ≃ₐ[F] L)
    have hcard : Nat.card (L ≃ₐ[F] L) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
    by_cases hg1 : g = 1
    · rw [← hg, hg1, one_smul]
    · obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[F] L)).1 hcard
      rw [← hg, hy g hg1, ← hy c hc1, hcw]
  have hf : w.asIdeal.inertiaDeg (𝓞 F) = 2 := by
    have := v.isPrime
    letI : Unique (v.asIdeal.primesOver (𝓞 L)) :=
      ⟨⟨⟨w.asIdeal, w.isPrime, hwv⟩⟩, fun P => Subtype.ext (huniq P.1 P.2.1 P.2.2)⟩
    have hs := Ideal.sum_ramification_inertia_eq_card (p := v.asIdeal) (S := 𝓞 L) (G := L ≃ₐ[F] L)
    rw [Fintype.sum_unique, IsGalois.card_aut_eq_finrank, h2] at hs
    have he := hU w hu
    rw [hu, Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot] at he
    change w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) = 2 at hs
    rwa [he, one_mul] at hs
  refine ⟨w, fun u => ⟨fun h => HeightOneSpectrum.ext (huniq _ u.isPrime ⟨by rw [← h]; rfl⟩), fun h => h ▸ hu⟩,
    hw, fun t ht => ?_⟩
  have h3 := frob_sq hq hσ
  rw [← ht] at h3
  rw [normV_under (K := F), hu, hf]
  exact ⟨h3.1, h3.2⟩
