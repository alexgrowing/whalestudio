import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHormanderIterationStepStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicSectionOfRapidCauchyDbarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEnergyOnCoverBallsLtTopOfSmoothStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.rough_hormander_compact : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ C : Cover A, ∃ K t0 : ℝ, 0 ≤ K ∧ ∀ (la : La) (t : ℝ), t0 ≤ t → CurvGe C la t → ∀ F0 : ι → Y → ℂ, A.IsSSec (A.kap + la) F0 → ∃ F : ι → Y → ℂ, A.IsSec (A.kap + la) F ∧ n0 A la (F0 - F) ≤ ENNReal.ofReal K * n1 C la F0 := by
  intro n Y _ _ _ _ _ _ ι La _ A C
  obtain ⟨K4, hK4, h4⟩ := GlobalTheory.T.exists_local_hormander_iteration_step n Y ι La A C
  refine ⟨4, 4 * K4 + 1, by norm_num, ?_⟩
  intro la t ht hC F0 hF0
  have tpos : 0 < t := by linarith
  have hq : K4 / t ≤ 1 / 4 := by rw [div_le_iff₀ tpos]; linarith
  have step : ∀ F : {F : ι → Y → ℂ // A.IsSSec (A.kap + la) F},
      ∃ G : {F : ι → Y → ℂ // A.IsSSec (A.kap + la) F},
        n0 A la (F.1 - G.1) ≤ ENNReal.ofReal (1 / 4) * n1 C la F.1 ∧
        n1 C la G.1 ≤ ENNReal.ofReal (1 / 4) * n1 C la F.1 := by
    intro F
    obtain ⟨G, hG, h1, h2⟩ := h4 la t tpos hC F.1 F.2
    have hq' : ENNReal.ofReal (K4 / t) ≤ ENNReal.ofReal (1 / 4) := ENNReal.ofReal_le_ofReal hq
    exact ⟨⟨G, hG⟩, h1.trans (by gcongr), h2.trans (by gcongr)⟩
  choose g hg using step
  let S : ℕ → {F : ι → Y → ℂ // A.IsSSec (A.kap + la) F} := fun m => g^[m] ⟨F0, hF0⟩
  have hS : ∀ m, S (m + 1) = g (S m) := fun m => Function.iterate_succ_apply' g m _
  have hN : n1 C la F0 < ⊤ := GlobalTheory.T.dbarEnergyOnCoverBalls_lt_top_of_smooth n Y ι La A C la F0 hF0
  have hq1 : ENNReal.ofReal (1 / 4) ≤ 1 := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
  have h1 : ∀ m, n1 C la (S m).1 ≤ ENNReal.ofReal ((1 / 4) ^ m) * n1 C la F0 := by
    intro m
    induction m with
    | zero => simp [S]
    | succ m ih =>
      rw [hS]
      refine (hg (S m)).2.trans ?_
      calc ENNReal.ofReal (1 / 4) * n1 C la (S m).1
          ≤ ENNReal.ofReal (1 / 4) * (ENNReal.ofReal ((1 / 4) ^ m) * n1 C la F0) := by
            gcongr
        _ = ENNReal.ofReal ((1 / 4) ^ (m + 1)) * n1 C la F0 := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num), pow_succ']
  have h0 : ∀ m, n0 A la ((S m).1 - (S (m + 1)).1) ≤
      ENNReal.ofReal ((n1 C la F0).toReal / 4 ^ m) := by
    intro m
    rw [hS]
    refine (hg (S m)).1.trans ?_
    refine (mul_le_of_le_one_left (zero_le) hq1).trans ((h1 m).trans (le_of_eq ?_))
    rw [show (n1 C la F0).toReal / 4 ^ m = (1 / 4) ^ m * (n1 C la F0).toReal by
        rw [one_div, inv_pow]; ring,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hN.ne]
  have hT : Tendsto (fun m => n1 C la (S m).1) atTop (𝓝 0) := by
    have hp : Tendsto (fun m : ℕ => ENNReal.ofReal ((1 / 4 : ℝ) ^ m)) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal
        (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num))
      simpa using this
    have hl := ENNReal.Tendsto.mul_const hp (Or.inr hN.ne)
    rw [zero_mul] at hl
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl
      (fun _ => zero_le) h1
  obtain ⟨G, hG, hfin⟩ := GlobalTheory.T.exists_holomorphicSection_of_rapid_cauchy_dbar n Y ι La A C la t (n1 C la F0).toReal (fun m => (S m).1)
    tpos hC ENNReal.toReal_nonneg (fun m => (S m).2) h0 hT
  refine ⟨G, hG, hfin.trans (le_of_eq ?_)⟩
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hN.ne]
