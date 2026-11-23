import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteAdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.GA
open scoped NumberField.AdeleRing Classical

namespace GlobalTheory.CompanionTheory.MajHeightK

theorem euclidNorm_le_sum {E : Type*} [NormedField E] (y : Fin 3 → E) :
    Reduction.euclidNorm y ≤ ∑ i, ‖y i‖ := by
  have h0 := norm_nonneg (y 0)
  have h1 := norm_nonneg (y 1)
  have h2 := norm_nonneg (y 2)
  rw [Reduction.euclidNorm, Fin.sum_univ_three, Fin.sum_univ_three]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  nlinarith [mul_nonneg h0 h1, mul_nonneg h0 h2, mul_nonneg h1 h2]

variable {K : Type} [Field K] [NumberField K]

theorem eq_of_quadratic (h2 : Module.finrank ℚ K = 2) (hc : IsTotallyComplex K)
    (w w' : InfinitePlace K) : w' = w := by
  have h := InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [IsTotallyComplex.nrRealPlaces_eq_zero K, h2] at h
  have hcomplex : InfinitePlace.nrComplexPlaces K = 1 := by omega
  have hcard : Fintype.card (InfinitePlace K) = 1 := by
    have := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
    rw [IsTotallyComplex.nrRealPlaces_eq_zero K, hcomplex] at this
    omega
  obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.1 hcard
  rw [ha w, ha w']

theorem infPart_le (h2 : Module.finrank ℚ K = 2) (hc : IsTotallyComplex K)
    (w : InfinitePlace K) (y : Fin 3 → K) :
    ∏ w' : InfinitePlace K,
        Reduction.euclidNorm (Reduction.infComp w' (Reduction.ratVec y)) ^ w'.mult
      ≤ (∑ i, w (y i)) ^ 2 := by
  have hmult : w.mult = 2 := InfinitePlace.mult_isComplex ⟨w, hc.isComplex w⟩
  have huniv : (Finset.univ : Finset (InfinitePlace K)) = {w} := by
    ext w'
    simp [eq_of_quadratic h2 hc w w']
  rw [huniv, Finset.prod_singleton, hmult]
  refine pow_le_pow_left₀ (Reduction.euclidNorm_nonneg _) ((euclidNorm_le_sum _).trans (le_of_eq ?_)) 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Reduction.infComp_ratVec, InfinitePlace.Completion.norm_coe]
  rfl

theorem norm_coe_le_one (v : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) :
    ‖Reduction.finComp v (Reduction.ratVec (fun _ : Fin 1 => (a : K))) 0‖ ≤ 1 := by
  refine Reduction.norm_le_one_of_mem v ?_
  rw [Reduction.finComp_ratVec]
  refine (coe_mem_adicCompletionIntegers_iff v (a : K)).2 ?_
  exact HeightOneSpectrum.valuation_le_one v a

theorem finPart_le_one (y : Fin 3 → K) (hy : ∀ i, ∃ a : 𝓞 K, (a : K) = y i) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖Reduction.finComp v (Reduction.ratVec y)‖ ≤ 1 := by
  have := finprod_induction (f := fun v : HeightOneSpectrum (𝓞 K) =>
      ‖Reduction.finComp v (Reduction.ratVec y)‖) (fun x : ℝ => 0 ≤ x ∧ x ≤ 1)
    ⟨zero_le_one, le_rfl⟩
    (fun a b ha hb => ⟨mul_nonneg ha.1 hb.1, mul_le_one₀ ha.2 hb.1 hb.2⟩)
    (fun v => ⟨norm_nonneg _, (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
      obtain ⟨a, ha⟩ := hy i
      have h := norm_coe_le_one v a
      rw [Reduction.finComp_ratVec] at h
      rw [Reduction.finComp_ratVec, ← ha]
      exact h⟩)
  exact this.2

theorem adelicNorm_ratVec_le : ∀ (K : Type) [Field K] [NumberField K],
    Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (w : InfinitePlace K) (M : ℕ), 0 < M →
    ∀ z : Fin 3 → K, (∀ i, ∃ a : 𝓞 K, (a : K) = (M : K) * z i) →
    Reduction.adelicNorm (Reduction.ratVec z : Fin 3 → 𝔸[K]) ≤
      (M : ℝ) ^ 2 * (∑ i, w (z i)) ^ 2 := by
  intro K _ _ h2 hc w M hM z hz
  by_cases h0 : z = 0
  · subst h0
    have h := infPart_le h2 hc w (0 : Fin 3 → K)
    have hnn : 0 ≤ ∏ w' : InfinitePlace K,
        Reduction.euclidNorm (Reduction.infComp w' (Reduction.ratVec (0 : Fin 3 → K))) ^ w'.mult :=
      Finset.prod_nonneg fun _ _ => pow_nonneg (Reduction.euclidNorm_nonneg _) _
    have hz0 : ∏ w' : InfinitePlace K,
        Reduction.euclidNorm (Reduction.infComp w' (Reduction.ratVec (0 : Fin 3 → K))) ^ w'.mult = 0 :=
      le_antisymm (by simpa using h) hnn
    rw [Reduction.adelicNorm, hz0, zero_mul]
    simp
  · have hMK : (M : K) ≠ 0 := by exact_mod_cast hM.ne'
    have hscale : Reduction.adelicNorm (Reduction.ratVec z : Fin 3 → 𝔸[K]) =
        Reduction.adelicNorm (Reduction.ratVec ((M : K) • z) : Fin 3 → 𝔸[K]) := by
      rw [Reduction.ratVec_smul, Reduction.adelicNorm_smul_rat (Reduction.hasFiniteContent_ratVec h0) hMK]
    rw [hscale, Reduction.adelicNorm]
    have hinf := infPart_le h2 hc w ((M : K) • z)
    have hfin := finPart_le_one ((M : K) • z) (fun i => by simpa using hz i)
    have hsum : (∑ i, w (((M : K) • z) i)) ^ 2 = (M : ℝ) ^ 2 * (∑ i, w (z i)) ^ 2 := by
      rw [← mul_pow, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [map_mul]
    rw [← hsum]
    calc _ ≤ (∑ i, w (((M : K) • z) i)) ^ 2 * 1 :=
          mul_le_mul hinf hfin (finprod_nonneg fun _ => norm_nonneg _) (by positivity)
      _ = _ := mul_one _

end GlobalTheory.CompanionTheory.MajHeightK
