import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfK
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormLeOfDet
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.HolomorphicBoundOfWeightedL2Statement
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.HolomorphicIsBigOOfHalfPowerBoundStatement

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.IntegralToOrder

open Filter Metric

theorem sum_sq_upper {n m : ℕ} {s : Fin m → V n → ℂ} (hs : ∀ k, DifferentiableAt ℂ (s k) 0)
    (hs0 : ∀ k, s k 0 = 0) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ z in 𝓝 (0 : V n), ∑ k, ‖s k z‖ ^ 2 ≤ B * ‖z‖ ^ 2 := by
  have hsk : ∀ k, ∃ C : ℝ, ∀ᶠ z in 𝓝 (0 : V n), ‖s k z‖ ≤ C * ‖z‖ := fun k => by
    have h := (hs k).hasFDerivAt.isBigO_sub
    simp only [hs0 k, sub_zero] at h
    exact h.bound
  choose C hC using hsk
  refine ⟨∑ k, C k ^ 2 + 1, by positivity, ?_⟩
  filter_upwards [eventually_all.mpr hC] with z hz
  calc ∑ k, ‖s k z‖ ^ 2 ≤ ∑ k, (C k * ‖z‖) ^ 2 :=
        Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hz k) 2
    _ = (∑ k, C k ^ 2) * ‖z‖ ^ 2 := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ _ := by nlinarith [sq_nonneg ‖z‖]

theorem lintegral_norm_lt_top {n : ℕ} (hn : 0 < n) {g : V n → ℂ} {S : V n → ℝ} {c B e ρ δ : ℝ}
    (hc : 0 < c) (hB : 0 < B) (he : 0 ≤ e) (hρ : 0 < ρ) (hδ : 0 < δ)
    (hlo : ∀ᶠ z in 𝓝 (0 : V n), c * ‖z‖ ^ 2 ≤ S z)
    (hup : ∀ᶠ z in 𝓝 (0 : V n), S z ≤ B * ‖z‖ ^ 2)
    (hint : ∫⁻ z in ball (0 : V n) ρ, ENNReal.ofReal (‖g z‖ ^ 2 * S z ^ (-e)) < ⊤) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ δ ∧
      ∫⁻ z in ball (0 : V n) ε, ENNReal.ofReal (‖g z‖ ^ 2 * (‖z‖ ^ 2) ^ (-e)) < ⊤ := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hlo.and hup)
  have : Nontrivial (V n) := ⟨⟨EuclideanSpace.single ⟨0, hn⟩ (1 : ℂ), 0, by
    intro h
    have h1 := congrArg (fun v : V n => v ⟨0, hn⟩) h
    simp at h1⟩⟩
  refine ⟨min (min ε ρ) δ, lt_min (lt_min hε hρ) hδ, min_le_right _ _, ?_⟩
  have hfin : ENNReal.ofReal (B ^ e) *
      ∫⁻ z in ball (0 : V n) ρ, ENNReal.ofReal (‖g z‖ ^ 2 * S z ^ (-e)) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint
  refine lt_of_le_of_lt ?_ hfin
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine le_trans ?_
    (lintegral_mono_set (ball_subset_ball ((min_le_left _ δ).trans (min_le_right ε ρ))))
  refine lintegral_mono_ae ?_
  have h0 : ∀ᵐ z ∂(volume.restrict (ball (0 : V n) (min (min ε ρ) δ))), z ≠ 0 :=
    ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton (0 : V n)))
  filter_upwards [h0, ae_restrict_mem measurableSet_ball] with z hz0 hz
  obtain ⟨h1, h2⟩ := hball z (ball_subset_ball ((min_le_left _ δ).trans (min_le_left ε ρ)) hz)
  have hz : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hSz : 0 < S z := lt_of_lt_of_le (by positivity) h1
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h3 : (B * ‖z‖ ^ 2) ^ (-e) ≤ S z ^ (-e) :=
    Real.rpow_le_rpow_of_nonpos hSz h2 (by linarith)
  have h4 : B ^ e * (B * ‖z‖ ^ 2) ^ (-e) = (‖z‖ ^ 2) ^ (-e) := by
    rw [Real.mul_rpow hB.le (by positivity), ← mul_assoc, ← Real.rpow_add hB]
    simp
  calc ‖g z‖ ^ 2 * (‖z‖ ^ 2) ^ (-e) = B ^ e * (‖g z‖ ^ 2 * (B * ‖z‖ ^ 2) ^ (-e)) := by
        rw [← h4]; ring
    _ ≤ B ^ e * (‖g z‖ ^ 2 * S z ^ (-e)) := by gcongr

end GlobalTheory.IntegralToOrder

namespace GlobalTheory

theorem isBigO_of_vanS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (Xa : ArchInM X) (Fl : FlatM X Xa) (a : ℕ) (g : Frame X.Ψ r → ℂ), DifferentiableOn ℂ g X.dom →
    VanS X Fl.xs Fl.s a g →
    ∀ j, (fun z : V (nd X) => g (cpt X (Fl.xs j) z)) =O[𝓝 0] fun z => ‖z‖ ^ a := by
  intro E _ _ _ r X Xa Fl a g hg hV j
  have hn : 0 < nd X := lt_of_lt_of_le (by norm_num) Xa.n_ge
  have hw0 : X.IsSec Xa.L Fl.w0 := Fl.weightForm_vanishes.1.1.1
  have hs : ∀ k, X.IsSec Xa.L (Fl.s k) := fun k => (Fl.s_van k).1.1.1
  have hs0 : ∀ k, Fl.s k (Fl.xs j) = 0 :=
    (Fl.S_eq _ (Fl.xs_mem j)).2 ⟨j, 1, X.Γ.one_mem, ExtFPf.oneF X, ExtFPf.oneF_mem X, by
      rw [FundSetPf.lact_one, ExtFPf.rmul_oneF]⟩
  have hdom : X.dom ∈ 𝓝 (cpt X (Fl.xs j) 0) := by
    rw [IW.cpt_zero]
    exact (FourierCoefficientDomain.isOpen_dom X).mem_nhds (Fl.xs_mem j)
  have hcd : Differentiable ℂ (cpt X (Fl.xs j)) := IW.cpt_diff X (Fl.xs j)
  have hat : ∀ P : Frame X.Ψ r → ℂ, DifferentiableOn ℂ P X.dom →
      DifferentiableAt ℂ (fun z : V (nd X) => P (cpt X (Fl.xs j) z)) 0 := fun P hP =>
    (hP.differentiableAt hdom).comp 0 (hcd 0)
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp only [pow_zero]
    exact (hat g hg).continuousAt.tendsto.isBigO_one ℝ
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.1 (hcd.continuous.continuousAt.preimage_mem_nhds hdom)
  have hgd : DifferentiableOn ℂ (fun z : V (nd X) => g (cpt X (Fl.xs j) z)) (Metric.ball 0 δ) :=
    hg.comp hcd.differentiableOn fun z hz => hsub hz
  obtain ⟨c, hc, hlo⟩ := OrderToIntegral.sum_sq_lower
    (w := fun z => Fl.w0 (cpt X (Fl.xs j) z)) (s := fun k z => Fl.s k (cpt X (Fl.xs j) z)) hn
    (hat _ hw0.1).continuousAt
    (by simpa only [IW.cpt_zero] using Fl.w0_ne j) (by simpa only [IW.cpt_zero] using hs0)
    (Fl.coord j)
  obtain ⟨B, hB, hup⟩ := IntegralToOrder.sum_sq_upper
    (s := fun k z => Fl.s k (cpt X (Fl.xs j) z)) (fun k => hat _ (hs k).1)
    (by simpa only [IW.cpt_zero] using hs0)
  obtain ⟨ρ, hρ, hint⟩ := hV j
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hn0 : (0 : ℝ) ≤ nd X := Nat.cast_nonneg _
  obtain ⟨ε, hε, hεδ, hint'⟩ := IntegralToOrder.lintegral_norm_lt_top
    (g := fun z => g (cpt X (Fl.xs j) z)) hn hc hB (by linarith) hρ hδ hlo hup hint
  have hexp : (a : ℝ) + (nd X : ℝ) - 1 / 2 = ((a : ℝ) - 1 / 2) + (nd X : ℝ) := by ring
  rw [hexp] at hint'
  have hgε := hgd.mono (Metric.ball_subset_ball hεδ)
  obtain ⟨C, η, hη, hb⟩ := GlobalTheory.T.holomorphic_bound_of_weighted_L2 (nd X) _ ε ((a : ℝ) - 1 / 2) hε (by linarith) hgε hint'
  exact GlobalTheory.T.holomorphic_isBigO_of_half_power_bound (nd X) a _ (min ε η) C hn (lt_min hε hη)
    (hgε.mono (Metric.ball_subset_ball (min_le_left _ _)))
    fun z hz0 hz => hb z hz0 (lt_of_lt_of_le hz (min_le_right _ _))

end GlobalTheory
