import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTopPullFS
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjDegGenDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenDegMatAct
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFrameChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMetricToFS
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

namespace ReductionToProjective

theorem powLog_shift_le (D : ℕ) {n j : ℕ} (hj : j ≤ n) :
    ((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1) ≤
      2 ^ (D + 1) * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by
  have h1 := powLog_mono D (show n + j ≤ 2 * n by omega)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h2 : 2 * Real.log ((n : ℝ) + 1) = Real.log (((n : ℝ) + 1) ^ 2) := by
    rw [Real.log_pow]; push_cast; ring
  have hlog : Real.log (((2 * n : ℕ) : ℝ) + 1) ≤ 2 * Real.log ((n : ℝ) + 1) := by
    rw [h2]
    exact Real.log_le_log (by positivity) (by push_cast; nlinarith)
  have hp : ((2 * n : ℕ) : ℝ) ^ D = 2 ^ D * (n : ℝ) ^ D := by push_cast; rw [mul_pow]
  calc ((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1)
      ≤ ((2 * n : ℕ) : ℝ) ^ D * Real.log (((2 * n : ℕ) : ℝ) + 1) := h1
    _ ≤ ((2 * n : ℕ) : ℝ) ^ D * (2 * Real.log ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = 2 ^ (D + 1) * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by rw [hp]; ring

theorem sub_chiP_isBigO (D k : ℕ) (δ C : ℝ) (hδ : 0 ≤ δ) (chi : ℕ → ℝ)
    (hlo : ∀ n : ℕ, k + 1 ≤ n → δ * chiP D (n - k) - C * (n : ℝ) ^ D * Real.log (n + 1) ≤ chi n)
    (hhi : ∀ n : ℕ, k + 1 ≤ n → chi n ≤ δ * chiP D (n + k) + C * (n : ℝ) ^ D * Real.log (n + 1)) :
    (fun n => chi n - δ * chiP D n) =O[atTop] fun n : ℕ => (n : ℝ) ^ D * Real.log ((n : ℝ) + 1) := by
  obtain ⟨C', hC'⟩ := exists_chiP_succ_sub_le D
  refine IsBigO.of_bound (δ * (k * (|C'| * 2 ^ (D + 1))) + |C|) ?_
  filter_upwards [eventually_ge_atTop (k + 1)] with n hn
  have hP0 : 0 ≤ (n : ℝ) ^ D * Real.log ((n : ℝ) + 1) := powLog_nonneg D n
  have hCP : C * (n : ℝ) ^ D * Real.log (n + 1) ≤ |C| * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self C) hP0
  have hCP' : -(|C| * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1))) ≤ C * (n : ℝ) ^ D * Real.log (n + 1) := by
    rw [mul_assoc, ← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_abs_le C) hP0
  have h2 : (1 : ℝ) ≤ 2 ^ (D + 1) := one_le_pow₀ (by norm_num)

  have hup : chiP D (n + k) - chiP D n ≤ k * (|C'| * 2 ^ (D + 1)) * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by
    refine (chiP_add_sub_le D C' hC' k n (by omega)).trans ?_
    calc ∑ j ∈ Finset.range k, |C'| * (((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1))
        ≤ ∑ j ∈ Finset.range k, |C'| * (2 ^ (D + 1) * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1))) := by
          refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ?_ (abs_nonneg C')
          exact powLog_shift_le D (by have := Finset.mem_range.1 hj; omega)
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

  have hdn : chiP D n - chiP D (n - k) ≤ k * (|C'| * 2 ^ (D + 1)) * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by
    have h := chiP_add_sub_le D C' hC' k (n - k) (by omega)
    rw [Nat.sub_add_cancel (by omega : k ≤ n)] at h
    refine h.trans ?_
    calc ∑ j ∈ Finset.range k, |C'| * (((n - k + j : ℕ) : ℝ) ^ D * Real.log (((n - k + j : ℕ) : ℝ) + 1))
        ≤ ∑ j ∈ Finset.range k, |C'| * (2 ^ (D + 1) * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1))) := by
          refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ?_ (abs_nonneg C')
          have hj' := Finset.mem_range.1 hj
          refine (powLog_mono D (show n - k + j ≤ n by omega)).trans ?_
          exact le_mul_of_one_le_left hP0 h2
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hlo' := hlo n hn
  have hhi' := hhi n hn
  have hu := mul_le_mul_of_nonneg_left hup hδ
  have hd := mul_le_mul_of_nonneg_left hdn hδ
  rw [Real.norm_eq_abs, Real.norm_of_nonneg hP0, abs_le]
  constructor
  · nlinarith
  · nlinarith

theorem defect_pullFS (hPB : ProjectionBounds.Statement) (hTop : TopPullFS.Statement) {D : ℕ} {Ω : Type}
    [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] (I : AllFam) (hI : I.IsFamily) (d : HSMDatum D Ω κ)
    (e : Fin (D + 1) → Ix κ) (hfr : IsProjFrame d.x e) (hFS : IsPullFS d.x e d.m) :
    (fun n => hsDefect D (resChi d) (top I d.x d.m D) n -
        (projDeg d.x e : ℝ) * hsDefect D (chiP D) (hhOf I D) n)
      =O[atTop] fun n : ℕ => (n : ℝ) ^ D * Real.log ((n : ℝ) + 1) := by
  obtain ⟨k, E, C, -, -, -, -, -, -, -, hs⟩ := hPB D Ω κ d e hfr hFS
  have ht := hTop D Ω κ I d.x d.m e hI d.arith d.smooth hfr hFS
  refine (sub_chiP_isBigO D k (projDeg d.x e) C (Nat.cast_nonneg _) (resChi d) (fun n hn => (hs n hn).1)
    (fun n hn => (hs n hn).2)).congr_left fun n => ?_
  simp only [hsDefect, ht]
  ring

theorem isLittleO_pow_pw (D : ℕ) : (fun n : ℕ => (n : ℝ) ^ D) =o[atTop] pw D :=
  (isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) (Nat.lt_succ_self D)).comp_tendsto tendsto_natCast_atTop_atTop

theorem proof (hPB : ProjectionBounds.Statement) (hCL : ChangeOfLattice.Statement)
    (hTop : TopPullFS.Statement) (hDeg : ProjDegGenDeg.Statement) (hInv : GenDegMatAct.Statement)
    (hFC : FrameChange.Statement) (hMF : MetricToFS.Statement) : ReductionToProjective.Statement := by
  intro D Ω _ _ κ _ I d hI
  refine ⟨fun e hfr hFS => defect_pullFS hPB hTop I hI d e hfr hFS, ?_⟩
  obtain ⟨B, d', e, hB, hx', hm', hfr', hidx⟩ := hFC D Ω κ d
  obtain ⟨d₀, hx₀, hFS₀, hmet⟩ := hMF D Ω κ I d' e hI hfr'
  have hfr₀ : IsProjFrame d₀.x e := hx₀ ▸ hfr'
  have hFS₀' : IsPullFS d₀.x e d₀.m := hx₀ ▸ hFS₀
  have h1 := (defect_pullFS hPB hTop I hI d₀ e hfr₀ hFS₀').trans_isLittleO (isLittleO_pow_mul_log D)
  rw [hx₀] at h1
  have h2 := (hCL D Ω κ I d.x B d.m d'.m hI d.arith d.indep hB d.smooth hm').trans_isLittleO
    (isLittleO_pow_pw D)
  rw [← hx'] at h2
  have hg : (genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 : ℝ) = (projDeg d'.x e : ℝ) := by
    have hd := hDeg D Ω κ d'.x e d'.arith hfr'
    have hi := hInv D Ω κ d.x B hB
    rw [← hx', hd] at hi
    rw [← hi]
    push_cast
    rfl
  rw [hg]
  refine ((h1.sub hmet).sub (hidx.add h2)).congr_left fun n => ?_
  simp only [hsDefect]
  ring

end ReductionToProjective

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
