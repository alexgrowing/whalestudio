import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJStandardLDefs

open MeasureTheory Filter Set Topology IsDedekindDomain NumberField NumberField.mixedEmbedding
open scoped NumberField.AdeleRing RestrictedProduct SchwartzMap Classical nonZeroDivisors

namespace GroundTheory.Automorphic

noncomputable section

namespace GJStandardL

open GodementJacquet GLnLocal GJMatrix GroundTheory.Global

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def entriesAt (v : HeightOneSpectrum (𝓞 K)) (y : Fin n × Fin n → FiniteAdeleRing (𝓞 K) K) :
    Matrix (Fin n) (Fin n) (v.adicCompletion K) :=
  Matrix.of fun i j ↦ y (i, j) v

theorem continuous_entriesAt (v : HeightOneSpectrum (𝓞 K)) : Continuous (entriesAt (n := n) v) :=
  continuous_matrix fun i j ↦ (RestrictedProduct.continuous_eval v).comp (continuous_apply (i, j))

def awayBoxN (S : Finset (HeightOneSpectrum (𝓞 K))) : Set (Fin n × Fin n → FiniteAdeleRing (𝓞 K) K) :=
  {y | ∀ ij, ∀ v ∉ S, y ij v ∈ v.adicCompletionIntegers K}

theorem isClopen_awayBoxN (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsClopen (awayBoxN (n := n) (K := K) S) := by
  have hA : IsClopen (GodementSection.awayIntegral S : Set (FiniteAdeleRing (𝓞 K) K)) :=
    ⟨AddSubgroup.isClosed_of_isOpen _ (GodementSection.isOpen_awayIntegral S),
      GodementSection.isOpen_awayIntegral S⟩
  have h : awayBoxN (n := n) (K := K) S =
      ⋂ ij : Fin n × Fin n, (fun y : Fin n × Fin n → FiniteAdeleRing (𝓞 K) K ↦ y ij) ⁻¹'
        (GodementSection.awayIntegral S : Set (FiniteAdeleRing (𝓞 K) K)) := by
    ext y
    simp only [awayBoxN, mem_iInter, mem_preimage, SetLike.mem_coe, GodementSection.mem_awayIntegral]
    rfl
  rw [h]
  exact isClopen_iInter_of_finite fun ij ↦ hA.preimage (continuous_apply ij)

def tensorFin (Φ : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ)
    (y : Fin n × Fin n → FiniteAdeleRing (𝓞 K) K) : ℂ :=
  ∏ᶠ v, Φ v (entriesAt v y)

theorem finite_setOf_not_integral (y : Fin n × Fin n → FiniteAdeleRing (𝓞 K) K) :
    {v : HeightOneSpectrum (𝓞 K) | ∃ ij, y ij v ∉ v.adicCompletionIntegers K}.Finite := by
  have h : {v : HeightOneSpectrum (𝓞 K) | ∃ ij, y ij v ∉ v.adicCompletionIntegers K} =
      ⋃ ij, {v | y ij v ∉ v.adicCompletionIntegers K} := by
    ext v
    simp
  rw [h]
  exact Set.finite_iUnion fun ij ↦ Filter.eventually_cofinite.1 (y ij).2

theorem integralIndicator_entriesAt {v : HeightOneSpectrum (𝓞 K)}
    {y : Fin n × Fin n → FiniteAdeleRing (𝓞 K) K} (h : ∀ ij, y ij v ∈ v.adicCompletionIntegers K) :
    integralIndicator (v.adicCompletion K) n (entriesAt v y) = 1 := by
  rw [integralIndicator, Set.indicator_of_mem, Pi.one_apply]
  rw [mem_integralMatrixSet]
  intro i j
  have := h (i, j)
  simp only [GroundTheory.Global.mem_valuationInteger_iff]
  exact this

theorem integralIndicator_entriesAt_of_not {v : HeightOneSpectrum (𝓞 K)}
    {y : Fin n × Fin n → FiniteAdeleRing (𝓞 K) K} {ij : Fin n × Fin n}
    (h : y ij v ∉ v.adicCompletionIntegers K) :
    integralIndicator (v.adicCompletion K) n (entriesAt v y) = 0 := by
  rw [integralIndicator, Set.indicator_of_notMem]
  rw [mem_integralMatrixSet]
  intro hall
  have := hall ij.1 ij.2
  simp only [GroundTheory.Global.mem_valuationInteger_iff] at this
  exact h this

theorem tensorFin_eq_indicator (S : Finset (HeightOneSpectrum (𝓞 K)))
    (Φ : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ)
    (h0 : ∀ v ∉ S, Φ v = integralIndicator (v.adicCompletion K) n) :
    tensorFin Φ = (awayBoxN S).indicator fun y ↦ ∏ v ∈ S, Φ v (entriesAt v y) := by
  funext y
  by_cases hy : y ∈ awayBoxN S
  · rw [Set.indicator_of_mem hy, tensorFin]
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv ↦ ?_
    by_contra hvS
    apply hv
    show Φ v (entriesAt v y) = 1
    rw [h0 v hvS]
    exact integralIndicator_entriesAt fun ij ↦ hy ij v hvS
  · rw [Set.indicator_of_notMem hy, tensorFin]
    simp only [awayBoxN, mem_ofPred_eq, not_forall] at hy
    obtain ⟨ij, v, hvS, hv⟩ := hy
    refine finprod_eq_zero _ v ?_ ?_
    · rw [h0 v hvS]
      exact integralIndicator_entriesAt_of_not hv
    · refine ((finite_setOf_not_integral y).union S.finite_toSet).subset fun w hw ↦ ?_
      by_contra hc
      simp only [mem_union, mem_ofPred_eq, not_or, not_exists, not_not, Finset.mem_coe] at hc
      apply hw
      show Φ w (entriesAt w y) = 1
      rw [h0 w hc.2]
      exact integralIndicator_entriesAt fun ij ↦ hc.1 ij

theorem tensorFin_mem (S : Finset (HeightOneSpectrum (𝓞 K)))
    (Φ : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ)
    (hS : ∀ v ∈ S, IsSchwartzBruhat (Φ v))
    (h0 : ∀ v ∉ S, Φ v = integralIndicator (v.adicCompletion K) n) :
    tensorFin Φ ∈ finiteSchwartzBruhatPi K := by
  rw [tensorFin_eq_indicator S Φ h0]
  refine (mem_finiteSchwartzBruhatPi K).2 ⟨?_, ?_⟩
  · refine GodementSectionLocal.isLocallyConstant_indicator (isClopen_awayBoxN S) ?_
    have heq : (fun y : Fin n × Fin n → FiniteAdeleRing (𝓞 K) K ↦ ∏ v ∈ S, Φ v (entriesAt v y)) =
        ∏ v ∈ S, fun y ↦ Φ v (entriesAt v y) := by
      funext y
      simp [Finset.prod_apply]
    rw [heq]
    exact Finset.prod_induction _ IsLocallyConstant (fun a b ha hb ↦ ha.mul hb)
      (IsLocallyConstant.const 1) fun v hv ↦ (hS v hv).1.comp_continuous (continuous_entriesAt v)
  ·
    have hb : ∀ v ∈ S, ∃ N : ℕ, ∀ x, Φ v x ≠ 0 → ∀ i j,
        ‖x i j‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ N := by
      intro v hv
      obtain ⟨C, hC⟩ := (hS v hv).2.isCompact.exists_bound_of_continuousOn
        (f := fun x : Matrix (Fin n) (Fin n) (v.adicCompletion K) ↦ ∑ i, ∑ j, ‖x i j‖)
        (Continuous.continuousOn (continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦
          (continuous_apply j |>.comp (continuous_apply i)).norm))
      have hN : (1 : ℝ) < Ideal.absNorm v.asIdeal := by
        exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
      obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt C hN
      refine ⟨N, fun x hx i j ↦ ?_⟩
      have hxC := hC x (subset_tsupport _ hx)
      rw [Real.norm_eq_abs] at hxC
      have h1 : ‖x i j‖ ≤ ∑ j, ‖x i j‖ :=
        Finset.single_le_sum (f := fun j ↦ ‖x i j‖) (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ j)
      have h2 : ∑ j, ‖x i j‖ ≤ ∑ i, ∑ j, ‖x i j‖ :=
        Finset.single_le_sum (f := fun i ↦ ∑ j, ‖x i j‖)
          (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) (Finset.mem_univ i)
      exact (h1.trans h2).trans ((le_abs_self _).trans hxC) |>.trans hN.le
    choose! N hN using hb
    set m : HeightOneSpectrum (𝓞 K) → ℤ := fun w ↦ if w ∈ S then -(N w : ℤ) else 0 with hm
    have hmfin : ∀ᶠ w in Filter.cofinite, m w = 0 := by
      rw [Filter.eventually_cofinite]
      refine S.finite_toSet.subset fun w hw ↦ ?_
      by_contra hwS
      exact hw (by simp only [hm, if_neg (fun h ↦ hwS (Finset.mem_coe.2 h))])
    set L : (FractionalIdeal (𝓞 K)⁰ K)ˣ := ∏ᶠ w, primeIdealUnit w ^ m w with hL
    have hcount : ∀ w, FractionalIdeal.count K w (L : FractionalIdeal (𝓞 K)⁰ K) = m w :=
      count_finprod_primeIdealUnit_zpow m hmfin
    refine HasCompactSupport.intro
      (isCompact_univ_pi fun _ : Fin n × Fin n ↦ isCompact_idealFiniteAdeles L) fun y hy ↦ ?_
    by_contra hne
    apply hy
    intro ij _
    rw [SetLike.mem_coe, mem_idealFiniteAdeles]
    intro w
    rw [hcount w]
    have hyB : y ∈ awayBoxN S := by
      by_contra h
      exact hne (Set.indicator_of_notMem h _)
    by_cases hw : w ∈ S
    · have hprod : ∏ v ∈ S, Φ v (entriesAt v y) ≠ 0 := by
        rwa [Set.indicator_of_mem hyB] at hne
      have hΦw : Φ w (entriesAt w y) ≠ 0 := Finset.prod_ne_zero_iff.1 hprod w hw
      have := GodementSection.valued_le_exp_of_norm_le (hN w hw (entriesAt w y) hΦw ij.1 ij.2)
      simp only [hm, if_pos hw, neg_neg]
      exact this
    · have hint : y ij w ∈ w.adicCompletionIntegers K := hyB ij w hw
      simp only [hm, if_neg hw, neg_zero, WithZero.exp_zero]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hint

theorem matrixTensor_mem (φ : 𝓢(Fin n × Fin n → mixedSpace K, ℂ)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (Φ : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ)
    (hS : ∀ v ∈ S, IsSchwartzBruhat (Φ v))
    (h0 : ∀ v ∉ S, Φ v = integralIndicator (v.adicCompletion K) n) :
    matrixTensor φ Φ ∈ matrixSchwartzBruhat K n := by
  rw [mem_matrixSchwartzBruhat]
  have h : (fun z : Fin n × Fin n → 𝔸[K] ↦ matrixTensor φ Φ (Matrix.of fun i j ↦ z (i, j))) =
      schwartzBruhatTensorPi φ (tensorFin Φ) := by
    funext z
    rfl
  rw [h]
  exact schwartzBruhatTensorPi_mem φ (tensorFin_mem S Φ hS h0)

theorem matrixTensor_coe (φ : 𝓢(Fin n × Fin n → mixedSpace K, ℂ))
    (Φ : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ)
    (g : AdelicGLn.AdelicGL K n) :
    matrixTensor φ Φ (g : Matrix (Fin n) (Fin n) 𝔸[K]) =
      archSchwartz φ (archComp K n g : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) *
        ∏ᶠ v, Φ v (localComp n v g : Matrix (Fin n) (Fin n) (v.adicCompletion K)) := by
  rw [matrixTensor, coe_archComp]
  simp only [coe_localComp]

end GJStandardL

end

end GroundTheory.Automorphic
