import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SmoothingFinite
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.MixedDifference

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace CuspidalSpectrum

open Reduction AutomorphicForm RightCosetSpace

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def unipBallMat (R : ℝ) : Set (ArchMatrix K n) := {A | ‖A - 1‖ ≤ R ∧ (A - 1) * (A - 1) = 0}

theorem isCompact_unipBallMat (R : ℝ) : IsCompact (unipBallMat (K := K) (n := n) R) := by
  refine (isCompact_closedBall (1 : ArchMatrix K n) R).of_isClosed_subset ?_ fun A hA => ?_
  · exact (isClosed_le (continuous_id.sub continuous_const).norm continuous_const).inter
      (isClosed_eq ((continuous_id.sub continuous_const).mul (continuous_id.sub continuous_const))
        continuous_const)
  · rw [Metric.mem_closedBall, dist_eq_norm]
    exact hA.1

theorem unipBallMat_subset_range (R : ℝ) :
    unipBallMat (K := K) (n := n) R ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n) := by
  intro A hA
  refine ⟨⟨A, 2 - A, ?_, ?_⟩, rfl⟩
  · have := hA.2
    calc A * (2 - A) = 1 - (A - 1) * (A - 1) := by noncomm_ring
      _ = 1 := by rw [this, sub_zero]
  · have := hA.2
    calc (2 - A) * A = 1 - (A - 1) * (A - 1) := by noncomm_ring
      _ = 1 := by rw [this, sub_zero]

def unipBall (R : ℝ) : Set (ArchUnits K n) :=
  (Units.val : ArchUnits K n → ArchMatrix K n) ⁻¹' unipBallMat R

theorem isCompact_unipBall (R : ℝ) : IsCompact (unipBall (K := K) (n := n) R) :=
  Units.isOpenEmbedding_val.isInducing.isCompact_preimage' (isCompact_unipBallMat R)
    (unipBallMat_subset_range R)

theorem altPoint_mul_altPoint {k : ℕ} {Y : Fin k → ArchMatrix K n} (hY : ∀ i j, Y i * Y j = 0)
    (ε : Fin k → Bool) : altPoint Y ε * altPoint Y ε = 0 := by
  unfold altPoint
  rw [Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs <;> simp [hY]

theorem norm_altPoint_le {k : ℕ} {Y : Fin k → ArchMatrix K n} {R : ℝ} (hR : ∀ i, ‖Y i‖ ≤ R)
    (ε : Fin k → Bool) : ‖altPoint Y ε‖ ≤ k * R := by
  unfold altPoint
  calc ‖∑ i, if ε i then Y i else 0‖ ≤ ∑ i : Fin k, ‖if ε i then Y i else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin k, R := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs
        · exact hR i
        · rw [norm_zero]; exact (norm_nonneg _).trans (hR i)
    _ = k * R := by simp

theorem altPoint_neg_mul {k : ℕ} (Y : Fin k → ArchMatrix K n) (a : ArchMatrix K n)
    (ε : Fin k → Bool) : altPoint (fun i => -(Y i * a)) ε = -(altPoint Y ε * a) := by
  unfold altPoint
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem val_inv_eq_of_val_eq {C : ArchUnits K n} {W : ArchMatrix K n} (hW : W * W = 0)
    (hC : (C : ArchMatrix K n) = 1 + W) : ((C⁻¹ : ArchUnits K n) : ArchMatrix K n) = 1 - W := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [hC]
  calc (1 + W) * (1 - W) = 1 - W * W := by noncomm_ring
    _ = 1 := by rw [hW, sub_zero]

section Diff

variable (ν : Measure (ArchUnits K n)) [ν.IsHaarMeasure] {β : ArchMatrix K n → ℝ}

theorem integrable_archConv_integrand (hβ : Continuous β) (hβc : HasCompactSupport β)
    (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n))
    (h : CompactlySupportedContinuousMap (normOneGL K n) ℂ) (C : ArchUnits K n)
    (w : normOneGL K n) :
    Integrable (fun A : ArchUnits K n =>
      (β ((C * A : ArchUnits K n) : ArchMatrix K n) : ℂ) * h ((archProj K n A)⁻¹ * w)) ν := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (Complex.continuous_ofReal.comp (hβ.comp (Units.continuous_val.comp
      (continuous_const.mul continuous_id)))).mul
      (h.continuous.comp ((continuous_archProj.inv).mul continuous_const))
  · refine HasCompactSupport.intro ((isCompact_unitsSupport hβc hβu).image
      (continuous_const_mul C⁻¹)) fun A hA => ?_
    have : ((C * A : ArchUnits K n) : ArchMatrix K n) ∉ tsupport β := fun h' =>
      hA ⟨C * A, h', by simp⟩
    rw [image_eq_zero_of_notMem_tsupport this, Complex.ofReal_zero, zero_mul]

theorem sum_altSign_archConvFun_eq (hβ : Continuous β) (hβc : HasCompactSupport β)
    (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n))
    (h : CompactlySupportedContinuousMap (normOneGL K n) ℂ) {k : ℕ} {Y : Fin k → ArchMatrix K n}
    (hY : ∀ i j, Y i * Y j = 0) {C : (Fin k → Bool) → ArchUnits K n}
    (hC : ∀ ε, ((C ε : ArchUnits K n) : ArchMatrix K n) = 1 + altPoint Y ε) (w : normOneGL K n) :
    ∑ ε, (altSign ε : ℂ) * archConvFun ν β h ((archProj K n (C ε))⁻¹ * w) =
      ∫ A : ArchUnits K n, ((altSum k β (fun i => -(Y i * (A : ArchMatrix K n)))
        (A : ArchMatrix K n) : ℝ) : ℂ) * h ((archProj K n A)⁻¹ * w) ∂ν := by
  have hterm : ∀ ε, archConvFun ν β h ((archProj K n (C ε))⁻¹ * w) =
      ∫ A : ArchUnits K n, (β ((A : ArchMatrix K n) + altPoint (fun i => -(Y i *
        (A : ArchMatrix K n))) ε) : ℂ) * h ((archProj K n A)⁻¹ * w) ∂ν := by
    intro ε
    rw [← map_inv, archConvFun_archProj_mul]
    refine integral_congr_ae (Eventually.of_forall fun A => ?_)
    simp only
    rw [Units.val_mul, val_inv_eq_of_val_eq (altPoint_mul_altPoint hY ε) (hC ε),
      altPoint_neg_mul, sub_mul, one_mul, sub_eq_add_neg]
  simp_rw [hterm, ← integral_const_mul]
  rw [← integral_finsetSum]
  · refine integral_congr_ae (Eventually.of_forall fun A => ?_)
    simp only
    rw [altSum_eq_sum, Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [zsmul_eq_mul, Complex.ofReal_mul, Complex.ofReal_intCast, mul_assoc]
  · intro ε _
    refine (Integrable.const_mul ?_ _)
    have := integrable_archConv_integrand ν hβ hβc hβu h (C ε)⁻¹ w
    refine this.congr (Eventually.of_forall fun A => ?_)
    simp only
    rw [Units.val_mul, val_inv_eq_of_val_eq (altPoint_mul_altPoint hY ε) (hC ε),
      altPoint_neg_mul, sub_mul, one_mul, sub_eq_add_neg]

theorem val_inv_mul_eq {k : ℕ} {Y : Fin k → ArchMatrix K n} (hY : ∀ i j, Y i * Y j = 0)
    {C : ArchUnits K n} {ε : Fin k → Bool} (hC : (C : ArchMatrix K n) = 1 + altPoint Y ε)
    (A : ArchUnits K n) :
    ((C⁻¹ * A : ArchUnits K n) : ArchMatrix K n) =
      (A : ArchMatrix K n) + altPoint (fun i => -(Y i * (A : ArchMatrix K n))) ε := by
  rw [Units.val_mul, val_inv_eq_of_val_eq (altPoint_mul_altPoint hY ε) hC, altPoint_neg_mul,
    sub_mul, one_mul, sub_eq_add_neg]

theorem mem_unipBall_of_val_eq {k : ℕ} {Y : Fin k → ArchMatrix K n} (hY : ∀ i j, Y i * Y j = 0)
    {R : ℝ} (hR : ∀ i, ‖Y i‖ ≤ R) {C : ArchUnits K n} {ε : Fin k → Bool}
    (hC : (C : ArchMatrix K n) = 1 + altPoint Y ε) : C ∈ unipBall (k * R) := by
  refine ⟨?_, ?_⟩
  · rw [hC, add_sub_cancel_left]
    exact norm_altPoint_le hR ε
  · rw [hC, add_sub_cancel_left]
    exact altPoint_mul_altPoint hY ε

theorem exists_norm_sum_altSign_archConvFun_le (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    (hβc : HasCompactSupport β)
    (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n))
    (h : CompactlySupportedContinuousMap (normOneGL K n) ℂ) (k : ℕ) (R : ℝ) :
    ∃ c : ℝ, ∀ (Y : Fin k → ArchMatrix K n), (∀ i j, Y i * Y j = 0) → (∀ i, ‖Y i‖ ≤ R) →
      ∀ (C : (Fin k → Bool) → ArchUnits K n),
        (∀ ε, ((C ε : ArchUnits K n) : ArchMatrix K n) = 1 + altPoint Y ε) → ∀ w : normOneGL K n,
        ‖∑ ε, (altSign ε : ℂ) * archConvFun ν β h ((archProj K n (C ε))⁻¹ * w)‖ ≤
          c * ∏ i, ‖Y i‖ := by
  obtain ⟨Bk, hBk⟩ := exists_norm_altSum_le hβ hβc k
  set S' := unipBall (K := K) (n := n) (k * R) *
    (Units.val : ArchUnits K n → ArchMatrix K n) ⁻¹' tsupport β
  have hS' : IsCompact S' := (isCompact_unipBall _).mul (isCompact_unitsSupport hβc hβu)
  obtain ⟨Rβ, hRβ⟩ := hS'.exists_bound_of_continuousOn
    (Units.continuous_val (M := ArchMatrix K n)).continuousOn
  obtain ⟨Mh, hMh⟩ := h.continuous.bounded_above_of_compact_support h.hasCompactSupport
  set Bk' := max Bk 0
  set Rβ' := max Rβ 0
  set Mh' := max Mh 0
  refine ⟨Bk' * Rβ' ^ k * Mh' * ν.real S', fun Y hY hR C hC w => ?_⟩
  rw [sum_altSign_archConvFun_eq ν hβ.continuous hβc hβu h hY hC w]
  have hpt : ∀ A : ArchUnits K n, ‖((altSum k β (fun i => -(Y i * (A : ArchMatrix K n)))
      (A : ArchMatrix K n) : ℝ) : ℂ) * h ((archProj K n A)⁻¹ * w)‖ ≤
      S'.indicator (fun _ => Bk' * (∏ i, ‖Y i‖) * Rβ' ^ k * Mh') A := by
    intro A
    by_cases hA : A ∈ S'
    · rw [indicator_of_mem hA, norm_mul, Complex.norm_real]
      refine mul_le_mul ?_ ((hMh _).trans (le_max_left _ _)) (norm_nonneg _) ?_
      · refine (hBk _ _).trans ?_
        have hA' : ‖(A : ArchMatrix K n)‖ ≤ Rβ' := (hRβ A hA).trans (le_max_left _ _)
        have hprod : ∏ i, ‖-(Y i * (A : ArchMatrix K n))‖ ≤ (∏ i, ‖Y i‖) * Rβ' ^ k := by
          rw [← Fin.prod_const, ← Finset.prod_mul_distrib]
          refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
          rw [norm_neg]
          exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hA' (norm_nonneg _))
        calc Bk * ∏ i, ‖-(Y i * (A : ArchMatrix K n))‖
            ≤ Bk' * ∏ i, ‖-(Y i * (A : ArchMatrix K n))‖ :=
              mul_le_mul_of_nonneg_right (le_max_left _ _)
                (Finset.prod_nonneg fun i _ => norm_nonneg _)
          _ ≤ Bk' * ((∏ i, ‖Y i‖) * Rβ' ^ k) :=
              mul_le_mul_of_nonneg_left hprod (le_max_right _ _)
          _ = Bk' * (∏ i, ‖Y i‖) * Rβ' ^ k := by ring
      · exact mul_nonneg (mul_nonneg (le_max_right _ _)
          (Finset.prod_nonneg fun i _ => norm_nonneg _)) (pow_nonneg (le_max_right _ _) _)
    · rw [indicator_of_notMem hA]
      have hzero : altSum k β (fun i => -(Y i * (A : ArchMatrix K n))) (A : ArchMatrix K n) = 0 := by
        rw [altSum_eq_sum]
        refine Finset.sum_eq_zero fun ε _ => ?_
        rw [← val_inv_mul_eq hY (hC ε) A]
        by_cases hs : (((C ε)⁻¹ * A : ArchUnits K n) : ArchMatrix K n) ∈ tsupport β
        · exact absurd ⟨C ε, mem_unipBall_of_val_eq hY hR (hC ε), _, hs, mul_inv_cancel_left _ _⟩ hA
        · rw [image_eq_zero_of_notMem_tsupport hs, smul_zero]
      rw [hzero, Complex.ofReal_zero, zero_mul, norm_zero]
  calc ‖∫ A : ArchUnits K n, ((altSum k β (fun i => -(Y i * (A : ArchMatrix K n)))
        (A : ArchMatrix K n) : ℝ) : ℂ) * h ((archProj K n A)⁻¹ * w) ∂ν‖
      ≤ ∫ A, S'.indicator (fun _ => Bk' * (∏ i, ‖Y i‖) * Rβ' ^ k * Mh') A ∂ν :=
        norm_integral_le_of_norm_le ((integrableOn_const hS'.measure_lt_top.ne).integrable_indicator
          hS'.measurableSet) (Eventually.of_forall hpt)
    _ = Bk' * (∏ i, ‖Y i‖) * Rβ' ^ k * Mh' * ν.real S' := by
        rw [integral_indicator hS'.measurableSet, setIntegral_const, smul_eq_mul, mul_comm]
    _ = Bk' * Rβ' ^ k * Mh' * ν.real S' * ∏ i, ‖Y i‖ := by ring

end Diff

end CuspidalSpectrum

end

end GroundTheory.Automorphic
