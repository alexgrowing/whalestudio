import Mathlib
open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem prod_norm_embeddings_eq_abs_norm (F : Type) [Field F] [NumberField F] (α : F) :
    ∏ σ : F →+* ℂ, ‖σ α‖ = ((|Algebra.norm ℚ α| : ℚ) : ℝ) := by
  have h2 : ∏ σ : F →+* ℂ, σ α = ∏ σ : F →ₐ[ℚ] ℂ, σ α :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom F ℂ) _ _ (fun σ => rfl)
  rw [← norm_prod, h2, ← Algebra.norm_eq_prod_embeddings ℚ ℂ α, eq_ratCast (algebraMap ℚ ℂ),
    Complex.norm_ratCast, Rat.cast_abs]

theorem norm_finite_embedding_eq_zpow (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (α : F) (k : ℤ)
    (h : v.valuation F α = WithZero.exp (-k)) :
    ‖FinitePlace.embedding v α‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-k) := by
  rw [FinitePlace.norm_def', h, WithZeroMulInt.toNNReal_neg_apply _ (WithZero.exp_ne_zero (a := -k))]
  have hk : Multiplicative.toAdd (WithZero.unzero (WithZero.exp_ne_zero (a := -k))) = -k := rfl
  rw [hk, NNReal.coe_zpow]
  rfl

theorem sum_log_embeddings_eq (F : Type) [Field F] [NumberField F]
    (n : HeightOneSpectrum (𝓞 F) →₀ ℤ) (α : F) (hα : α ≠ 0)
    (hv : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F α = WithZero.exp (-(n v))) :
    ∑ σ : F →+* ℂ, Real.log ‖σ α‖ =
      n.sum fun v k => (k : ℝ) * Real.log (Ideal.absNorm v.asIdeal) := by
  have hσ : ∀ σ ∈ (Finset.univ : Finset (F →+* ℂ)), ‖σ α‖ ≠ 0 := fun σ _ =>
    norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hα)
  rw [← Real.log_prod hσ, prod_norm_embeddings_eq_abs_norm]
  have hv2 : ∀ v : HeightOneSpectrum (𝓞 F),
      ‖FinitePlace.embedding v α‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(n v)) :=
    fun v => norm_finite_embedding_eq_zpow F v α (n v) (hv v)
  have key : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v α‖
      = ∏ᶠ w : FinitePlace F, w α := by
    rw [← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := F)).symm]
    simp only [FinitePlace.equivHeightOneSpectrum_symm_apply]
  have hprod : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v α‖
      = ∏ v ∈ n.support, (Ideal.absNorm v.asIdeal : ℝ) ^ (-(n v)) := by
    simp only [hv2]
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hvs
    rw [Function.mem_mulSupport] at hvs
    by_contra hn
    simp only [Finset.mem_coe, Finsupp.mem_support_iff, not_not] at hn
    apply hvs
    simp [hn]
  have E0 := FinitePlace.prod_eq_inv_abs_norm hα
  rw [← key, hprod] at E0
  have hfac : ∀ v ∈ n.support, (Ideal.absNorm v.asIdeal : ℝ) ^ (-(n v)) ≠ 0 := by
    intro v _
    apply zpow_ne_zero
    exact_mod_cast (mt Ideal.absNorm_eq_zero_iff.mp v.ne_bot)
  have L := congrArg Real.log E0
  push_cast at L ⊢
  rw [Real.log_prod hfac, Real.log_inv] at L
  simp only [Real.log_zpow] at L
  rw [Finsupp.sum]
  have hneg : ∑ v ∈ n.support, ((-(n v) : ℤ) : ℝ) * Real.log (Ideal.absNorm v.asIdeal)
      = -∑ v ∈ n.support, (n v : ℝ) * Real.log (Ideal.absNorm v.asIdeal) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    push_cast
    ring
  linarith

end GlobalTheory.CompanionTheory.Ar.Flat
