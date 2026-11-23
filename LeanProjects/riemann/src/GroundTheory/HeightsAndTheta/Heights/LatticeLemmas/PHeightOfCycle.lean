import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsFibreMahler
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.GaussSum
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ContinuousHermNormGroup
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FieldChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField

noncomputable section

namespace HeightOfCycle

variable {K : Type*} [Field K] [NumberField K]

theorem gaussNorm_eq_iSup {ι : Type*} (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {f : MvPolynomial ι K} (hf : f ≠ 0) (S : Finset (ι →₀ ℕ)) (hS : f.support ⊆ S) :
    gaussNorm v f = ⨆ m : S, FinitePlace.equivHeightOneSpectrum.symm v (f.coeff m) := by
  have e : ∀ m, FinitePlace.equivHeightOneSpectrum.symm v (f.coeff m) =
      NumberField.HeightOneSpectrum.adicAbv K v (f.coeff m) := fun m ↦ by
    rw [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]
  simp_rw [e]
  obtain ⟨m, hm, hmax⟩ := exists_gaussNormOf_eq (NumberField.HeightOneSpectrum.adicAbv K v) hf
  have : Nonempty S := ⟨⟨m, hS hm⟩⟩
  apply le_antisymm
  · rw [gaussNorm_eq_gaussNormOf, hmax]
    exact le_ciSup (f := fun m : S ↦ NumberField.HeightOneSpectrum.adicAbv K v (f.coeff m))
      (Set.finite_range _).bddAbove ⟨m, hS hm⟩
  · exact ciSup_le fun m ↦ le_gaussNormOf _ f m

theorem finsum_log_gaussNorm_map {E : Type*} [Field E] [NumberField E] [Algebra E K] {ι : Type*}
    {P : MvPolynomial ι E} (hP : P ≠ 0) :
    ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v (P.map (algebraMap E K))) =
      Module.finrank E K *
        ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), Real.log (gaussNorm v P) := by
  have hPK : P.map (algebraMap E K) ≠ 0 :=
    fun h0 ↦ hP (MvPolynomial.map_injective _ (algebraMap E K).injective (by rw [h0, _root_.map_zero]))
  obtain ⟨m0, hm0⟩ := support_nonempty.mpr hP
  have hy : (fun m : P.support ↦ P.coeff m) ≠ 0 :=
    Function.ne_iff.mpr ⟨⟨m0, hm0⟩, mem_support_iff.mp hm0⟩
  have eK : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      gaussNorm v (P.map (algebraMap E K)) =
        ⨆ m : P.support, FinitePlace.equivHeightOneSpectrum.symm v (algebraMap E K (P.coeff m)) :=
    fun v ↦ by
      rw [gaussNorm_eq_iSup v hPK P.support (support_map_subset _ _)]
      simp_rw [coeff_map]
  have eE : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E),
      gaussNorm v P = ⨆ m : P.support, FinitePlace.equivHeightOneSpectrum.symm v (P.coeff m) :=
    fun v ↦ gaussNorm_eq_iSup v hP P.support subset_rfl
  simp_rw [eK, eE]
  rw [finsum_comp_equiv FinitePlace.equivHeightOneSpectrum.symm
      (f := fun w : FinitePlace K ↦ Real.log (⨆ m : P.support, w (algebraMap E K (P.coeff m)))),
    finsum_comp_equiv FinitePlace.equivHeightOneSpectrum.symm
      (f := fun w : FinitePlace E ↦ Real.log (⨆ m : P.support, w (P.coeff m)))]
  exact finsum_log_iSup_algebraMap hy

theorem finsum_log_gaussNorm_prod {ι α : Type*} (s : Finset α) (L : α → MvPolynomial ι K)
    (hL : ∀ q, L q ≠ 0) :
    ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v (∏ q ∈ s, L q)) =
      ∑ q ∈ s, ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v (L q)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    rw [← C_1]
    simp_rw [gaussNorm_C, map_one, Real.log_one, finsum_zero]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, finsum_log_gaussNorm_mul (hL a)
      (Finset.prod_ne_zero_iff.mpr fun q _ ↦ hL q), ih, Finset.sum_insert ha]

end HeightOfCycle

open HeightOfCycle in

theorem HeightOfCycle.proof (h1 : HeightOfPoint.Statement) (h2 : FibreMahlerForms.Statement) :
    HeightOfCycle.Statement := by
  intro F _ _ W _ _ _ _ h n w hw E _ _ _ K _ _ _ _ _ m yv hyv c hc P hP

  have hL : ∀ q, (∑ k, C (yv q (w k)) * X k : MvPolynomial (Fin n) K) ≠ 0 := by
    intro q h0
    apply hyv q
    have hle : Submodule.span (𝓞 F) (Set.range w) ≤ LinearMap.ker (yv q) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have := congrArg (coeff (Finsupp.single k 1)) h0
      simp only [coeff_sum, coeff_C_mul, coeff_X, coeff_zero] at this
      rw [Finset.sum_eq_single k (fun j _ hj ↦ by
        rw [if_neg (fun e ↦ hj (Finsupp.single_left_injective one_ne_zero e)), mul_zero])
        (by simp)] at this
      simpa using this
    rw [hw, top_le_iff, LinearMap.ker_eq_top] at hle
    exact hle
  have hprod : (∏ q, ∑ k, C (yv q (w k)) * X k : MvPolynomial (Fin n) K) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun q _ ↦ hL q
  have hPne : P ≠ 0 := by
    rintro rfl
    rw [_root_.map_zero] at hP
    exact mul_ne_zero (C_ne_zero.mpr hc) hprod hP.symm
  have hr : (Module.finrank E K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'

  have hpt : ∀ q, pointHeight h (yv q) = (Module.finrank ℚ K : ℝ)⁻¹ *
      ((∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          Real.log (gaussNorm v (∑ k, C (yv q (w k)) * X k))) +
        ∑ τ : K →+* ℂ, Real.log (archDualNorm h τ (yv q))) := by
    intro q
    obtain ⟨hloc, hht⟩ := h1 F W h n w hw K (yv q) (hyv q)
    have hex : ∃ x, yv q x ≠ 0 := by
      by_contra hne
      push Not at hne
      exact hyv q (LinearMap.ext hne)
    rw [pointHeight, hht _ (Classical.epsilon_spec hex)]
    congr 2
    exact finsum_congr fun v ↦ by rw [(hloc v).2]

  have hfin : ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), Real.log (gaussNorm v P) =
      (Module.finrank E K : ℝ)⁻¹ *
        ((∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
            Real.log (NumberField.HeightOneSpectrum.adicAbv K v c)) +
          ∑ q, ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
            Real.log (gaussNorm v (∑ k, C (yv q (w k)) * X k))) := by
    rw [eq_inv_mul_iff_mul_eq₀ hr, ← finsum_log_gaussNorm_map hPne, hP,
      finsum_log_gaussNorm_mul (C_ne_zero.mpr hc) hprod,
      finsum_log_gaussNorm_prod Finset.univ (fun q ↦ ∑ k, C (yv q (w k)) * X k) hL]
    simp_rw [gaussNorm_C]

  have harch : ∑ σ : E →+* ℂ, (fibreMahler h (σ.comp (algebraMap F E)) w (P.map σ) +
        m * (harmonic (Module.finrank (𝓞 F) W - 1) : ℝ) / 2) =
      (Module.finrank E K : ℝ)⁻¹ * ∑ τ : K →+* ℂ,
        (Real.log ‖τ c‖ + ∑ q, Real.log (archDualNorm h τ (yv q))) := by
    rw [eq_inv_mul_iff_mul_eq₀ hr, ← sum_embeddings_restrict (K := E) (L := K)
      (fun σ : E →+* ℂ ↦ fibreMahler h (σ.comp (algebraMap F E)) w (P.map σ) +
        m * (harmonic (Module.finrank (𝓞 F) W - 1) : ℝ) / 2)]
    refine Finset.sum_congr rfl fun τ _ ↦ ?_
    have e1 : (τ.comp (algebraMap E K)).comp (algebraMap F E) = τ.comp (algebraMap F K) := by
      rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
    have e2 : P.map (τ.comp (algebraMap E K)) =
        C (τ c) * ∏ q, ∑ k, C (τ (yv q (w k))) * X k := by
      rw [← MvPolynomial.map_map, hP]
      simp only [map_mul, map_prod, map_sum, map_C, map_X]
    rw [e1, e2, h2 F W h n w hw K τ m yv hyv (τ c) ((map_ne_zero τ).mpr hc)]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  rw [hfin, harch, Finset.sum_add_distrib, finsum_log_adicAbv hc, sum_log_norm_embeddings hc,
    Finset.sum_comm (f := fun τ q ↦ Real.log (archDualNorm h τ (yv q)))]
  simp_rw [hpt]
  rw [← Module.finrank_mul_finrank ℚ E K, ← Finset.mul_sum, Finset.sum_add_distrib]
  push_cast
  field_simp
  ring

end

end GroundTheory.Heights₂.Heights
