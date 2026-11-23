import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SecondDifferenceInvPowBoundStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.LatSumZ

theorem difdif (L : ℕ) (hL : 0 < L) (v : ℤ × ℤ) (F : ℤ × ℤ → ℂ) (x : ℤ × ℤ) :
    dif L v (dif L v F) x = ((L : ℂ) ^ 2)⁻¹ * ∑ r' ∈ Finset.range L, ∑ r ∈ Finset.range L,
      (F x - F (x + (r : ℤ) • v) - F (x + (r' : ℤ) • v) + F (x + (r' : ℤ) • v + (r : ℤ) • v)) := by
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  set S := ∑ r ∈ Finset.range L, F (x + (r : ℤ) • v)
  set T := ∑ r' ∈ Finset.range L, ∑ r ∈ Finset.range L, F (x + (r' : ℤ) • v + (r : ℤ) • v)
  have e : ∑ r' ∈ Finset.range L, ∑ r ∈ Finset.range L,
      (F x - F (x + (r : ℤ) • v) - F (x + (r' : ℤ) • v) + F (x + (r' : ℤ) • v + (r : ℤ) • v))
      = (L : ℂ) * L * F x - L * S - L * S + T := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, S, T]
    rw [← Finset.mul_sum]; ring
  have e2 : ∑ r' ∈ Finset.range L, (F (x + (r' : ℤ) • v) - (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L, F (x + (r' : ℤ) • v + (r : ℤ) • v))
      = S - (L : ℂ)⁻¹ * T := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [e]
  simp only [dif]
  rw [e2]
  field_simp
  ring

theorem trm_zero (j : ℕ) (y : ℂ) : trm j 0 y = (y ^ j)⁻¹ := by
  simp [trm]

theorem lin_shift (τ : ℍ) (x v : ℤ × ℤ) (r : ℕ) :
    (((x + (r : ℤ) • v).1 : ℤ) : ℂ) * (τ : ℂ) + (((x + (r : ℤ) • v).2 : ℤ) : ℂ)
      = ((x.1 : ℂ) * τ + x.2) + (r : ℂ) * ((v.1 : ℂ) * τ + v.2) := by
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  push_cast; ring

theorem lin_shift2 (τ : ℍ) (x v : ℤ × ℤ) (r' r : ℕ) :
    (((x + (r' : ℤ) • v + (r : ℤ) • v).1 : ℤ) : ℂ) * (τ : ℂ) + (((x + (r' : ℤ) • v + (r : ℤ) • v).2 : ℤ) : ℂ)
      = ((x.1 : ℂ) * τ + x.2) + (r' : ℂ) * ((v.1 : ℂ) * τ + v.2) + (r : ℂ) * ((v.1 : ℂ) * τ + v.2) := by
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  push_cast; ring

theorem difdif_bound (j L : ℕ) (v : ℤ × ℤ) (τ : ℍ) (hj : 1 ≤ j) (hL : 0 < L) (C : ℝ)
    (hC : ∀ z a b : ℂ, z ≠ 0 → 4 * ‖a‖ ≤ ‖z‖ → 4 * ‖b‖ ≤ ‖z‖ →
      ‖(z ^ j)⁻¹ - ((z + a) ^ j)⁻¹ - ((z + b) ^ j)⁻¹ + ((z + a + b) ^ j)⁻¹‖ ≤ C * ‖a‖ * ‖b‖ / ‖z‖ ^ (j + 2))
    (x : ℤ × ℤ)
    (h1 : 1 ≤ ‖(x.1 : ℂ) * τ + x.2‖) (h4 : 4 * (L * ‖(v.1 : ℂ) * τ + v.2‖) ≤ ‖(x.1 : ℂ) * τ + x.2‖) :
    ‖dif L v (dif L v (fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2))) x‖
      ≤ max C 0 * (L * ‖(v.1 : ℂ) * τ + v.2‖) ^ 2 / ‖(x.1 : ℂ) * τ + x.2‖ ^ 3 := by
  set z : ℂ := (x.1 : ℂ) * τ + x.2 with hz
  set w : ℂ := (v.1 : ℂ) * τ + v.2 with hw
  set B : ℝ := max C 0 * (L * ‖w‖) ^ 2 / ‖z‖ ^ 3 with hB
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at h1; linarith
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hterm : ∀ r' ∈ Finset.range L, ∀ r ∈ Finset.range L,
      ‖trm j 0 z - trm j 0 (z + (r : ℂ) * w) - trm j 0 (z + (r' : ℂ) * w)
        + trm j 0 (z + (r' : ℂ) * w + (r : ℂ) * w)‖ ≤ B := by
    intro r' hr' r hr
    have hr'L : (r' : ℝ) ≤ L := by exact_mod_cast (Finset.mem_range.mp hr').le
    have hrL : (r : ℝ) ≤ L := by exact_mod_cast (Finset.mem_range.mp hr).le
    have na : ‖(r' : ℂ) * w‖ ≤ L * ‖w‖ := by
      rw [norm_mul, Complex.norm_natCast]; exact mul_le_mul_of_nonneg_right hr'L (norm_nonneg _)
    have nb : ‖(r : ℂ) * w‖ ≤ L * ‖w‖ := by
      rw [norm_mul, Complex.norm_natCast]; exact mul_le_mul_of_nonneg_right hrL (norm_nonneg _)
    have key := hC z ((r' : ℂ) * w) ((r : ℂ) * w) hz0 (by linarith) (by linarith)
    simp only [trm_zero]
    have eq : (z ^ j)⁻¹ - ((z + (r : ℂ) * w) ^ j)⁻¹ - ((z + (r' : ℂ) * w) ^ j)⁻¹
        + ((z + (r' : ℂ) * w + (r : ℂ) * w) ^ j)⁻¹
        = (z ^ j)⁻¹ - ((z + (r' : ℂ) * w) ^ j)⁻¹ - ((z + (r : ℂ) * w) ^ j)⁻¹
        + ((z + (r' : ℂ) * w + (r : ℂ) * w) ^ j)⁻¹ := by ring
    rw [eq]
    refine key.trans ?_
    have hpow : ‖z‖ ^ 3 ≤ ‖z‖ ^ (j + 2) := pow_le_pow_right₀ h1 (by omega)
    have hp3 : 0 < ‖z‖ ^ 3 := by positivity
    have hM : 0 ≤ max C 0 := le_max_right _ _
    calc C * ‖(r' : ℂ) * w‖ * ‖(r : ℂ) * w‖ / ‖z‖ ^ (j + 2)
        ≤ max C 0 * ‖(r' : ℂ) * w‖ * ‖(r : ℂ) * w‖ / ‖z‖ ^ (j + 2) := by
          gcongr; exact le_max_left _ _
      _ ≤ max C 0 * (L * ‖w‖) * (L * ‖w‖) / ‖z‖ ^ (j + 2) := by gcongr
      _ ≤ max C 0 * (L * ‖w‖) * (L * ‖w‖) / ‖z‖ ^ 3 := by
          apply div_le_div_of_nonneg_left (by positivity) hp3 hpow
      _ = B := by rw [hB]; ring
  rw [difdif L hL v _ x]
  simp only [lin_shift τ, lin_shift2 τ]
  rw [← hz, ← hw]
  calc ‖((L : ℂ) ^ 2)⁻¹ * ∑ r' ∈ Finset.range L, ∑ r ∈ Finset.range L,
        (trm j 0 z - trm j 0 (z + (r : ℂ) * w) - trm j 0 (z + (r' : ℂ) * w)
          + trm j 0 (z + (r' : ℂ) * w + (r : ℂ) * w))‖
      ≤ ((L : ℝ) ^ 2)⁻¹ * ∑ r' ∈ Finset.range L, ∑ r ∈ Finset.range L, B := by
        rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
        gcongr
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r' hr' => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r hr => hterm r' hr' r hr)
    _ = B := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

theorem latsum_summable : ∀ (j L : ℕ) (v : ℤ × ℤ) (τ : ℍ), 1 ≤ j → 0 < L →
    Summable fun x => ‖dif L v (dif L v (fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2))) x‖ := by
  intro j L v τ hj hL
  obtain ⟨C, hC⟩ := GlobalTheory.T.second_difference_inv_pow_bound j
  set w : ℂ := (v.1 : ℂ) * τ + v.2 with hw
  set R : ℝ := max (4 * (L * ‖w‖)) 1 with hR
  have hrτ : 0 < EisensteinSeries.r τ := EisensteinSeries.r_pos τ
  set M : ℝ := R / EisensteinSeries.r τ + 1 with hM
  set K : ℝ := max C 0 * (L * ‖w‖) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  rw [← (finTwoArrowEquiv ℤ).summable_iff]
  have hs : Summable fun y : Fin 2 → ℤ => K * (EisensteinSeries.r τ ^ 3)⁻¹ * ‖y‖ ^ (-(3 : ℝ)) :=
    (EisensteinSeries.summable_one_div_norm_rpow (by norm_num : (2 : ℝ) < 3)).mul_left _
  refine Summable.of_norm_bounded_eventually hs ?_
  have hev : ∀ᶠ y : Fin 2 → ℤ in cofinite, M ≤ ‖y‖ := by
    rw [← cocompact_eq_cofinite]
    exact tendsto_norm_cocompact_atTop.eventually_ge_atTop M
  filter_upwards [hev] with y hy
  have hR1 : 1 ≤ R := le_max_right _ _
  have hMpos : 0 < M := by positivity
  have hy0 : y ≠ 0 := by
    intro h; rw [h, norm_zero] at hy; linarith
  have hlow := EisensteinSeries.r_mul_max_le τ hy0
  have hRle : R ≤ EisensteinSeries.r τ * ‖y‖ := by
    have : EisensteinSeries.r τ * M ≤ EisensteinSeries.r τ * ‖y‖ := mul_le_mul_of_nonneg_left hy hrτ.le
    have h2 : EisensteinSeries.r τ * M = R + EisensteinSeries.r τ := by
      rw [hM]; field_simp
    linarith
  have hxe : (((finTwoArrowEquiv ℤ y).1 : ℤ) : ℂ) * (τ : ℂ) + (((finTwoArrowEquiv ℤ y).2 : ℤ) : ℂ)
      = (y 0 : ℂ) * τ + y 1 := by simp
  have hzR : R ≤ ‖((finTwoArrowEquiv ℤ y).1 : ℂ) * τ + ((finTwoArrowEquiv ℤ y).2 : ℂ)‖ := by
    rw [hxe]; linarith
  have h1 : 1 ≤ ‖((finTwoArrowEquiv ℤ y).1 : ℂ) * τ + ((finTwoArrowEquiv ℤ y).2 : ℂ)‖ :=
    le_trans (le_max_right _ _) hzR
  have h4 : 4 * (L * ‖w‖) ≤ ‖((finTwoArrowEquiv ℤ y).1 : ℂ) * τ + ((finTwoArrowEquiv ℤ y).2 : ℂ)‖ :=
    le_trans (le_max_left _ _) hzR
  have hb := difdif_bound j L v τ hj hL C hC (finTwoArrowEquiv ℤ y) h1 h4
  rw [Function.comp_apply, norm_norm]
  refine hb.trans ?_
  rw [hxe] at h1 ⊢
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hprod : 0 < EisensteinSeries.r τ * ‖y‖ := mul_pos hrτ hypos
  have hrp : ‖y‖ ^ (-(3 : ℝ)) = (‖y‖ ^ 3)⁻¹ := by
    rw [Real.rpow_neg (norm_nonneg _), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hrp, ← hw]
  calc max C 0 * (L * ‖w‖) ^ 2 / ‖(y 0 : ℂ) * τ + y 1‖ ^ 3
      ≤ K / (EisensteinSeries.r τ * ‖y‖) ^ 3 := by
        rw [hK]
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact pow_le_pow_left₀ hprod.le hlow 3
    _ = K * (EisensteinSeries.r τ ^ 3)⁻¹ * (‖y‖ ^ 3)⁻¹ := by
        rw [mul_pow]; field_simp

end GlobalTheory.LatSumZ
