import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import GroundTheory.GlobalFields.TateThesis.TraceDualLattice
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIndependentLeOfDualMin
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

namespace GlobalTheory.CompanionTheory.Ar.Cusp

section ShortIntegers

open NumberField.InfinitePlace NumberField.mixedEmbedding Module GroundTheory.Global
open scoped ComplexConjugate nonZeroDivisors Classical

variable (K : Type) [Field K] [NumberField K]

theorem sum_norm_sq_embeddings (x : K) :
    ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 = ∑ w, (mixedEmbedding K x).1 w ^ 2 +
      ∑ w, 2 * ‖(mixedEmbedding K x).2 w‖ ^ 2 := by
  have h3 : ∀ w : InfinitePlace K,
      ∑ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => InfinitePlace.mk φ = w), ‖φ x‖ ^ 2 =
        mult w * (w x) ^ 2 := by
    intro w
    have h : ∀ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => InfinitePlace.mk φ = w),
        ‖φ x‖ ^ 2 = (w x) ^ 2 := by
      intro φ hφ
      rw [← (Finset.mem_filter.mp hφ).2, InfinitePlace.apply]
    rw [Finset.sum_congr rfl h, Finset.sum_const, card_filter_mk_eq, nsmul_eq_mul]
  rw [← Finset.sum_fiberwise Finset.univ (fun φ : K →+* ℂ => InfinitePlace.mk φ)
    (fun φ => ‖φ x‖ ^ 2)]
  simp_rw [h3]
  rw [sum_eq_sum_add_sum]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mult_isReal, Nat.cast_one, one_mul, mixedEmbedding_apply_isReal,
      ← InfinitePlace.norm_embedding_of_isReal w.2 x, Real.norm_eq_abs, sq_abs]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mult_isComplex, mixedEmbedding_apply_isComplex, InfinitePlace.norm_embedding_eq]
    norm_num

omit [Field K] [NumberField K] in
theorem re_conj_sqrtTwo_smul_mul (z : ℂ) :
    (conj ((√2 : ℝ) • z) * ((√2 : ℝ) • z)).re = 2 * ‖z‖ ^ 2 := by
  rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re, _root_.norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by norm_num)]

theorem norm_sq_mixedToEuclidean (x : mixedSpace K) :
    ‖mixedToEuclidean K x‖ ^ 2 = ∑ w, x.1 w ^ 2 + ∑ w, 2 * ‖x.2 w‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, mixedToEuclidean, ContinuousLinearEquiv.trans_apply,
    inner_toMixed_symm]
  simp only [mapComplexCoord_apply, sqrtTwoSMulComplex_apply]
  congr 1
  · exact Finset.sum_congr rfl fun w _ => by ring
  · exact Finset.sum_congr rfl fun w _ => re_conj_sqrtTwo_smul_mul _

theorem norm_sq_mixedToEuclideanConj (x : mixedSpace K) :
    ‖mixedToEuclideanConj K x‖ ^ 2 = ∑ w, x.1 w ^ 2 + ∑ w, 2 * ‖x.2 w‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, mixedToEuclideanConj, ContinuousLinearEquiv.trans_apply,
    inner_toMixed_symm]
  simp only [mapComplexCoord_apply, sqrtTwoSMulConj_apply]
  congr 1
  · exact Finset.sum_congr rfl fun w _ => by ring
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [re_conj_sqrtTwo_smul_mul, Complex.norm_conj]

noncomputable def integersEuclid : Submodule ℤ (euclidean.mixedSpace K) :=
  ZLattice.comap ℝ (idealLattice K 1) (mixedToEuclidean K).symm.toLinearMap

instance : DiscreteTopology (integersEuclid K) := by
  rw [integersEuclid]
  infer_instance

instance : IsZLattice ℝ (integersEuclid K) := by
  simp_rw [integersEuclid]
  infer_instance

theorem mem_integersEuclid {z : euclidean.mixedSpace K} :
    z ∈ integersEuclid K ↔ ∃ a : 𝓞 K, mixedToEuclidean K (mixedEmbedding K (a : K)) = z := by
  change (mixedToEuclidean K).symm z ∈ idealLattice K 1 ↔ _
  rw [mem_idealLattice]
  constructor
  · rintro ⟨y, hy, h⟩
    have hy1 : y ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by simpa using hy
    obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hy1
    refine ⟨a, ?_⟩
    change mixedToEuclidean K (mixedEmbedding K (algebraMap (𝓞 K) K a)) = z
    rw [h, ContinuousLinearEquiv.apply_symm_apply]
  · rintro ⟨a, rfl⟩
    refine ⟨(a : K), ?_, by simp⟩
    have : (a : K) ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) :=
      (FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩
    simpa using this

theorem norm_sq_mixedToEuclidean_embedding (x : K) :
    ‖mixedToEuclidean K (mixedEmbedding K x)‖ ^ 2 = ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  rw [norm_sq_mixedToEuclidean, sum_norm_sq_embeddings]

theorem finrank_div_rootDiscr_sq_le_norm_sq {y : euclidean.mixedSpace K} (hy : y ≠ 0)
    (h : ∀ x ∈ integersEuclid K, ∃ m : ℤ, ⟪x, y⟫_ℝ = m) :
    (finrank ℚ K : ℝ) / rootDiscr K ^ 2 ≤ ‖y‖ ^ 2 := by
  set y0 := (mixedToEuclideanConj K).symm y with hy0
  have hmem : y0 ∈ idealLattice K (traceDualIdeal K 1) := by
    rw [mem_idealLattice_traceDualIdeal_iff]
    intro x hx
    obtain ⟨m, hm⟩ := h (mixedToEuclidean K x) (by
      change (mixedToEuclidean K).symm (mixedToEuclidean K x) ∈ idealLattice K 1
      simpa using hx)
    refine ⟨m, ?_⟩
    rw [mixedTraceForm_comm, mixedTraceForm_eq_inner, hy0,
      ContinuousLinearEquiv.apply_symm_apply, hm]
  obtain ⟨t, ht, hty⟩ := (mem_idealLattice K _).1 hmem
  have hyy : y = mixedToEuclideanConj K (mixedEmbedding K t) := by
    rw [hty, hy0, ContinuousLinearEquiv.apply_symm_apply]
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hy (by simpa using hyy)
  have ht' : t ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
    rw [← GlobalTheory.dual_one_eq_inv_differentIdeal]
    simpa [coe_traceDualIdeal] using ht
  have hb := GlobalTheory.finrank_div_rootDiscr_sq_le_sum_sq ht' ht0
  rw [hyy, norm_sq_mixedToEuclideanConj, ← sum_norm_sq_embeddings]
  exact hb

theorem exists_short_integers :
    ∃ a : Fin (finrank ℚ K) → 𝓞 K, LinearIndependent ℚ (fun i => (a i : K)) ∧
      ∀ i (σ : K →+* ℂ), ‖σ (a i)‖ ≤ finrank ℚ K * rootDiscr K := by
  have hfr : finrank ℝ (euclidean.mixedSpace K) = finrank ℚ K := euclidean.finrank K
  have hn : (0 : ℝ) < finrank ℚ K := by exact_mod_cast finrank_pos
  have hrd : 0 < rootDiscr K := by
    rw [rootDiscr_def]
    exact Real.rpow_pos_of_pos (by exact_mod_cast abs_pos.2 (discr_ne_zero K)) _
  have hμ : 0 < √(finrank ℚ K : ℝ) / rootDiscr K := by positivity
  have hdual : ∀ y : euclidean.mixedSpace K, y ≠ 0 →
      (∀ x ∈ integersEuclid K, ∃ m : ℤ, ⟪x, y⟫_ℝ = m) →
      √(finrank ℚ K : ℝ) / rootDiscr K ≤ ‖y‖ := by
    intro y hy h
    refine (sq_le_sq₀ hμ.le (norm_nonneg y)).1 ?_
    rw [div_pow, Real.sq_sqrt hn.le]
    exact finrank_div_rootDiscr_sq_le_norm_sq K hy h
  obtain ⟨b, hbL, hbi, hbn⟩ := exists_independent_le_of_dual_min (euclidean.mixedSpace K) (integersEuclid K) _ hμ hdual
  have hbound : (finrank ℚ K : ℝ) ^ (3 / 2 : ℝ) / (√(finrank ℚ K : ℝ) / rootDiscr K) =
      finrank ℚ K * rootDiscr K := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hn, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
    have : √(finrank ℚ K : ℝ) ≠ 0 := (Real.sqrt_pos.2 hn).ne'
    field_simp
  have hb' : ∀ i : Fin (finrank ℚ K), ∃ a : 𝓞 K,
      mixedToEuclidean K (mixedEmbedding K (a : K)) = b (Fin.cast hfr.symm i) :=
    fun i => (mem_integersEuclid K).1 (hbL _)
  choose a ha using hb'
  refine ⟨a, ?_, fun i σ => ?_⟩
  · have h1 : LinearIndependent ℤ (fun i : Fin (finrank ℚ K) => b (Fin.cast hfr.symm i)) :=
      (hbi.comp _ (Fin.cast_injective _)).restrict_scalars (R := ℤ)
        (fun x y h => by simpa using h)
    rw [← LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)]
    let g : K →ₗ[ℤ] euclidean.mixedSpace K := AddMonoidHom.toIntLinearMap
      { toFun := fun x => mixedToEuclidean K (mixedEmbedding K x)
        map_zero' := by simp
        map_add' := fun x y => by simp }
    have hg : (⇑g ∘ fun i => ((a i : 𝓞 K) : K)) = fun i => b (Fin.cast hfr.symm i) := funext ha
    refine LinearIndependent.of_comp g ?_
    rw [hg]
    exact h1
  · have h2 : ‖σ (a i)‖ ^ 2 ≤ ∑ τ : K →+* ℂ, ‖τ (a i)‖ ^ 2 :=
      Finset.single_le_sum (f := fun τ : K →+* ℂ => ‖τ (a i)‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ σ)
    rw [← norm_sq_mixedToEuclidean_embedding, ha i] at h2
    have h3 := hbn (Fin.cast hfr.symm i)
    rw [show ((finrank ℝ (euclidean.mixedSpace K) : ℕ) : ℝ) = finrank ℚ K by rw [hfr], hbound] at h3
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
      (h2.trans (pow_le_pow_left₀ (norm_nonneg _) h3 2))

end ShortIntegers

theorem exists_full_family_conjugates_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    ∃ a : Fin (Module.finrank ℚ E) → 𝓞 E, LinearIndependent ℚ (fun i => (a i : E)) ∧
      ∀ i (σ : E →+* ℂ), ‖σ (a i)‖ ≤ Module.finrank ℚ E * hostRd E := by
  intro E _ _ _
  have h : hostRd E = rootDiscr E := by simp [hostRd, rootDiscr_def]
  rw [h]
  exact exists_short_integers E

end GlobalTheory.CompanionTheory.Ar.Cusp
