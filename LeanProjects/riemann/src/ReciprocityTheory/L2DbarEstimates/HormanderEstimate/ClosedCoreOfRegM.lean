import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.ExistsLintegralCompactLe
import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.RegMDbEqZeroOfNotMem

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

theorem enorm_integral_sub_mul_le (n : ℕ) {M : Type*} [MeasurableSpace M] (z : M → V n)
    (ψ : M → ℝ) (hψ : Measurable ψ) (f F g : M → ℂ) (hf : AEStronglyMeasurable f (vol n z))
    (hF : AEStronglyMeasurable F (vol n z)) (hg : AEStronglyMeasurable g (vol n z)) :
    ‖∫ x, (f x - F x) * g x ∂vol n z‖ₑ ≤
      wint n z (fun x => F x - f x) ψ ^ (1 / 2 : ℝ) *
        (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2 * Real.exp (ψ x)) ∂vol n z) ^ (1 / 2 : ℝ) := by
  have hw : AEMeasurable (fun x => ENNReal.ofReal (‖F x - f x‖ * Real.exp (-ψ x / 2))) (vol n z) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((hF.sub hf).norm.aemeasurable.mul (hψ.neg.div_const 2).exp.aemeasurable)
  have hv : AEMeasurable (fun x => ENNReal.ofReal (‖g x‖ * Real.exp (ψ x / 2))) (vol n z) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (hg.norm.aemeasurable.mul (hψ.div_const 2).exp.aemeasurable)
  have hpt : ∀ x, ‖(f x - F x) * g x‖ₑ = ENNReal.ofReal (‖F x - f x‖ * Real.exp (-ψ x / 2)) *
      ENNReal.ofReal (‖g x‖ * Real.exp (ψ x / 2)) := by
    intro x
    rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ‖F x - f x‖ * Real.exp (-ψ x / 2)),
      ← ofReal_norm_eq_enorm, norm_mul, norm_sub_rev (f x) (F x)]
    congr 1
    have h1 : Real.exp (-ψ x / 2) * Real.exp (ψ x / 2) = 1 := by
      rw [← Real.exp_add, show -ψ x / 2 + ψ x / 2 = 0 by ring, Real.exp_zero]
    calc ‖F x - f x‖ * ‖g x‖
        = ‖F x - f x‖ * ‖g x‖ * (Real.exp (-ψ x / 2) * Real.exp (ψ x / 2)) := by rw [h1, mul_one]
      _ = ‖F x - f x‖ * Real.exp (-ψ x / 2) * (‖g x‖ * Real.exp (ψ x / 2)) := by ring
  have hw2 : ∀ x, ENNReal.ofReal (‖F x - f x‖ * Real.exp (-ψ x / 2)) ^ (2:ℝ) =
      ENNReal.ofReal (‖F x - f x‖ ^ 2 * Real.exp (-ψ x)) := by
    intro x
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.rpow_two, mul_pow,
      sq (Real.exp _), ← Real.exp_add]
    congr 3 <;> ring
  have hv2 : ∀ x, ENNReal.ofReal (‖g x‖ * Real.exp (ψ x / 2)) ^ (2:ℝ) =
      ENNReal.ofReal (‖g x‖ ^ 2 * Real.exp (ψ x)) := by
    intro x
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.rpow_two, mul_pow,
      sq (Real.exp _), ← Real.exp_add]
    congr 3 <;> ring
  calc ‖∫ x, (f x - F x) * g x ∂vol n z‖ₑ
      ≤ ∫⁻ x, ‖(f x - F x) * g x‖ₑ ∂vol n z := by
        first
          | exact enorm_integral_le_lintegral_enorm _
          | exact ennnorm_integral_le_lintegral_ennnorm _
    _ = ∫⁻ x, ((fun x => ENNReal.ofReal (‖F x - f x‖ * Real.exp (-ψ x / 2))) *
          (fun x => ENNReal.ofReal (‖g x‖ * Real.exp (ψ x / 2)))) x ∂vol n z :=
        lintegral_congr (fun x => hpt x)
    _ ≤ (∫⁻ x, ENNReal.ofReal (‖F x - f x‖ * Real.exp (-ψ x / 2)) ^ (2:ℝ) ∂vol n z) ^ (1 / (2:ℝ)) *
          (∫⁻ x, ENNReal.ofReal (‖g x‖ * Real.exp (ψ x / 2)) ^ (2:ℝ) ∂vol n z) ^ (1 / (2:ℝ)) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq _
          (by first
            | exact Real.HolderConjugate.two_two
            | exact Real.IsConjExponent.two
            | (constructor <;> norm_num)) hw hv
    _ = _ := by simp only [hw2, hv2, wint]

theorem closedCore_of_regM (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hReg : RegMStatement n M) :
    ClosedCoreStatement n M := by
  intro z hz ψ hψ F f hF hfm hlim
  haveI := vol_isFiniteMeasureOnCompacts n z hz
  have hψm : Measurable ψ := hψ.measurable
  have hFc : ∀ k, Continuous (F k) := fun k => Smooth.continuous n z hz _ (Holo.smooth n z _ (hF k))
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, ∀ k ≥ k₀, wint n z (fun x => F k x - f x) ψ < ⊤ := by
    obtain ⟨k₀, hk⟩ := Filter.eventually_atTop.1 ((ENNReal.tendsto_nhds_zero.1 hlim) 1 one_pos)
    exact ⟨k₀, fun k hk' => lt_of_le_of_lt (hk k hk') ENNReal.one_lt_top⟩
  have hwsym : ∀ k, wint n z (fun x => f x - F k x) ψ = wint n z (fun x => F k x - f x) ψ := by
    intro k
    unfold wint
    congr 1
    funext x
    rw [norm_sub_rev]

  have hLoc : LocalL2Isometry (vol n z) (fun x => f x - F k₀ x) := by
    refine ⟨hfm.sub (hFc k₀).aestronglyMeasurable, fun C hC => ?_⟩
    obtain ⟨c, hc⟩ := exists_lintegral_compact_le n z ψ hψ C hC
    refine lt_of_le_of_lt (hc _) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
    rw [hwsym]
    exact hk₀ k₀ le_rfl

  have hweak : ∀ φ : M → ℂ, IsTest n z φ → ∀ j : Fin n,
      ∫ x, (f x - F k₀ x) * db n z j φ x ∂vol n z = 0 := by
    intro φ hφ j
    have hDc : Continuous (db n z j φ) := Smooth.continuous n z hz _ (Smooth.db n z j φ hφ.1)
    have hDs : HasCompactSupport (db n z j φ) := hφ.2.mono' ((subset_tsupport _).trans (tsupport_db_subset n z j φ))
    have hFD : ∀ k, Integrable (fun x => F k x * db n z j φ x) (vol n z) := fun k =>
      ((hFc k).mul hDc).integrable_of_hasCompactSupport hDs.mul_left
    by_cases hgi : Integrable (fun x => (f x - F k₀ x) * db n z j φ x) (vol n z)
    swap
    · exact integral_undef hgi
    have key : ∀ k, ∫ x, (f x - F k x) * db n z j φ x ∂vol n z =
        ∫ x, (f x - F k₀ x) * db n z j φ x ∂vol n z := by
      intro k
      have h0k := integral_holo_mul_db n z hz _ (hF k) φ hφ j
      have h00 := integral_holo_mul_db n z hz _ (hF k₀) φ hφ j
      calc ∫ x, (f x - F k x) * db n z j φ x ∂vol n z
          = ∫ x, ((f x - F k₀ x) * db n z j φ x -
              (F k x * db n z j φ x - F k₀ x * db n z j φ x)) ∂vol n z := by
            congr 1
            funext x
            ring
        _ = ∫ x, (f x - F k₀ x) * db n z j φ x ∂vol n z -
              ∫ x, (F k x * db n z j φ x - F k₀ x * db n z j φ x) ∂vol n z :=
            integral_sub hgi ((hFD k).sub (hFD k₀))
        _ = ∫ x, (f x - F k₀ x) * db n z j φ x ∂vol n z -
              (∫ x, F k x * db n z j φ x ∂vol n z - ∫ x, F k₀ x * db n z j φ x ∂vol n z) :=
            congrArg (fun s => ∫ x, (f x - F k₀ x) * db n z j φ x ∂vol n z - s)
              (integral_sub (hFD k) (hFD k₀))
        _ = ∫ x, (f x - F k₀ x) * db n z j φ x ∂vol n z := by
            rw [h0k, h00, sub_zero, sub_zero]
    have hB := lintegral_db_test_lt_top n z hz ψ hψ φ hφ j
    have hbound : ∀ k, ‖∫ x, (f x - F k₀ x) * db n z j φ x ∂vol n z‖ₑ ≤
        wint n z (fun x => F k x - f x) ψ ^ (1 / 2 : ℝ) *
          (∫⁻ x, ENNReal.ofReal (‖db n z j φ x‖ ^ 2 * Real.exp (ψ x)) ∂vol n z) ^ (1 / 2 : ℝ) := by
      intro k
      rw [← key k]
      exact enorm_integral_sub_mul_le n z ψ hψm f (F k) (db n z j φ) hfm
        (hFc k).aestronglyMeasurable hDc.aestronglyMeasurable
    have hlim2 : Tendsto (fun k => wint n z (fun x => F k x - f x) ψ ^ (1 / 2 : ℝ) *
        (∫⁻ x, ENNReal.ofReal (‖db n z j φ x‖ ^ 2 * Real.exp (ψ x)) ∂vol n z) ^ (1 / 2 : ℝ))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun k => wint n z (fun x => F k x - f x) ψ ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
        have := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hlim
        rwa [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
      have h2 := ENNReal.Tendsto.mul_const h1
        (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hB.ne))
      rwa [zero_mul] at h2
    have h0 : ‖∫ x, (f x - F k₀ x) * db n z j φ x ∂vol n z‖ₑ = 0 :=
      le_antisymm (ge_of_tendsto' hlim2 hbound) (zero_le')
    exact enorm_eq_zero.1 h0
  obtain ⟨G, hG, hfG⟩ := hReg z hz _ hLoc hweak
  refine ⟨fun x => G x + F k₀ x, fun e he => (hG e he).add (hF k₀ e he), ?_⟩
  filter_upwards [hfG] with x hx
  rw [← hx]
  ring

end

end ReciprocityTheory.L2DbarEstimates.F
