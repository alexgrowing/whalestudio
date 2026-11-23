import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published
open scoped Pointwise

private theorem frob_of_smul {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {q : ℕ} {g σ : G E Ω} (hσ : IsFrob (F := E) (g • A) q σ) :
    IsFrob (F := E) A q (g⁻¹ * σ * g) := by
  have hm : ∀ x, g x ∈ g • A ↔ x ∈ A := fun x => ValuationSubring.smul_mem_pointwise_smul_iff
  refine ⟨?_, fun x hx => ?_⟩
  · have h1 : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h1, inv_smul_smul]
  · have h1 := hσ.2 (g x) (by rwa [ValuationSubring.valuation_le_one_iff, hm,
      ← ValuationSubring.valuation_le_one_iff])
    have e : σ (g x) - g x ^ q = g ((g⁻¹ * σ * g) x - x ^ q) := by
      rw [map_sub, map_pow, AlgEquiv.mul_apply, AlgEquiv.mul_apply, mul_inv_apply]
    rwa [e, valuation_lt_one_iff', ← map_inv₀, hm, hm, map_eq_zero_iff _ g.injective,
      ← valuation_lt_one_iff'] at h1

private theorem normV_under' {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

private theorem one_lt_normV' {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) : 1 < normV w :=
  NumberField.HeightOneSpectrum.one_lt_absNorm w

private theorem normV_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {q : ℕ} (hq : 1 < q)
    (h : ∀ x : 𝓞 K, x - x ^ q ∈ w.asIdeal) : normV w ≤ q := by
  have := w.isMaximal
  letI : Field (𝓞 K ⧸ w.asIdeal) := Ideal.Quotient.field _
  have : Finite (𝓞 K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI := Fintype.ofFinite (𝓞 K ⧸ w.asIdeal)
  have e : normV w = Fintype.card (𝓞 K ⧸ w.asIdeal) := by
    show Ideal.absNorm w.asIdeal = _
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [e]
  by_contra hlt
  refine FiniteField.X_pow_card_sub_X_ne_zero (𝓞 K ⧸ w.asIdeal) hq
    (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ Finset.univ (fun y _ => ?_) ?_)
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    have := Ideal.Quotient.eq.2 (h x)
    rw [map_pow] at this
    rw [eval_sub, eval_pow, eval_X, ← this, sub_self]
  · rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ hq, Finset.card_univ]
    exact not_le.1 hlt

theorem UpperTheory.frobenius_sign_compatibility :
    UpperTheory.V.Af.Bc.SignFrob := by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ l _ ι δ hδ w hur A' hA'
  refine ⟨hur A' hA', fun σ' hσ' => ?_⟩
  have : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans F E Ω⟩
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  have hv : IsPlaceOver A (w.under (𝓞 F)) := fun x => by
    rw [IsScalarTower.algebraMap_apply F E Ω]
    exact hA (algebraMap (𝓞 F) (𝓞 E) x)
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hv hA'
  have hσ := frob_of_smul hσ'
  have e : δ σ' = δ (g⁻¹ * σ' * g) := by
    rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
  rw [map_inv, e]
  generalize g⁻¹ * σ' * g = σ at hσ
  split_ifs with hq
  · obtain ⟨φ, hφ⟩ := exists_isFrob hA
    have hφ' : IsFrob (F := F) A (normV (w.under (𝓞 F))) (res F Ω E φ) := by
      rw [← hq]
      exact ⟨hφ.1, hφ.2⟩
    have h1 := hur A hv _ (inv_mul_mem_Ine_of_isFrob hσ hφ')
    rw [map_mul, (hδ.1 _).2 ⟨φ, rfl⟩, mul_one, map_inv] at h1
    rw [h1]; simp
  · rcases hδ.2 σ with h1 | h1
    · exfalso
      obtain ⟨ψ, rfl⟩ := (hδ.1 σ).1 h1
      have hle : normV w ≤ normV (w.under (𝓞 F)) := by
        refine normV_le w (one_lt_normV' _) fun x => ?_
        rw [← hA]
        have hx : A.valuation (algebraMap E Ω x) ≤ 1 := by
          rw [A.valuation_le_one_iff]
          have hi : IsIntegral ℤ (algebraMap E Ω x) := x.isIntegral_coe.algebraMap
          obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).1 (hi.tower_top (A := A))
          rw [← hy]
          exact y.2
        have h2 := hσ.2 _ hx
        have h3 : res F Ω E ψ (algebraMap E Ω x) = algebraMap E Ω x := ψ.commutes x
        rw [h3] at h2
        simpa using h2
      refine hq (le_antisymm hle ?_)
      have h4 := one_lt_normV' w
      rw [normV_under' (K := F) w] at h4 ⊢
      refine Nat.le_self_pow (fun h0 => ?_) _
      rw [h0] at h4
      simp at h4
    · rw [h1]; simp
