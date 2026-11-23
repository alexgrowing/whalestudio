import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpCStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfL
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInvariantChartSetLeMulFundamentalSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHormanderPeakCutoffSingularWeightsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlurisubharmonicDecreasingLimitExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicWeightedSquareIntegrableVanishesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeakExtensionVanishOtherOrbitPointsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
open scoped ContDiff

namespace GlobalTheory.HormanderPeak

open scoped ENNReal

theorem hormander_peak : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x : Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 → C * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ a : ℝ) - la τ b) → (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → C * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ b : ℝ) - la τ a) → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → ∃ (F : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ) (P0 : Frame X.Ψ r → ℂ), DifferentiableOn ℂ F (ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) ∧ ReciprocityTheory.ChartRestriction.G.AR.Up.IsBEq X la P0 ∧ (∀ z ∈ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x, P0 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = F z) ∧ P0 x = 1 ∧ (∀ γ ∈ X.Γ, γ ≠ 1 → P0 (lact γ x) = 0) ∧ ReciprocityTheory.ChartRestriction.G.AR.Up.InAt X x (ReciprocityTheory.ChartRestriction.G.AR.Up.IW.Wpsi X la (fun _ => 0)) (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) F ∧ ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) * ReciprocityTheory.ChartRestriction.G.AR.Up.IW.Wpsi X la (fun _ => 0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x) ≤ ENNReal.ofReal (Real.exp (C * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8))) * ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) := by

  classical
  obtain ⟨C1, hC1, hW⟩ := GlobalTheory.T.exists_hormanderPeak_cutoff_singularWeights
  refine ⟨C1 + 2, by linarith, ?_⟩
  intro E _ _ _ r X la x hp0 hp0r ho hgap hbar hinj
  have hr2 : 2 ≤ r := by omega
  obtain ⟨t0⟩ : Nonempty X.Ψ := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases h : τ ∈ X.Ψ
    · exact ⟨⟨τ, h⟩⟩
    · by_cases h' : ComplexEmbedding.conjugate τ ∈ X.Ψ
      · exact ⟨⟨_, h'⟩⟩
      · exact absurd ((X.cmType τ).2 h') h
  have hnd : 0 < nd X :=
    Fintype.card_pos_iff.2 ⟨⟨t0, ⟨(⟨1, by omega⟩, ⟨0, by omega⟩), by simp [Fin.lt_def]⟩⟩⟩
  have hcard : (1 : ℝ) ≤ X.Ψ.card := by
    have : 0 < X.Ψ.card := Finset.card_pos.2 ⟨t0.1, t0.2⟩
    exact_mod_cast this
  have hfr : 1 ≤ (X.Ψ.card : ℝ) * r := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr2
    nlinarith
  set S : ℝ := (∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8 with hSdef
  have hf8 : 1 ≤ ((X.Ψ.card : ℝ) * r) ^ 8 := one_le_pow₀ hfr
  have hS1 : 1 ≤ S := by
    have h2 : 0 ≤ ∑ τ, ∑ a, |(la τ a : ℝ)| :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hgap' : ∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 →
      C1 * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ a : ℝ) - la τ b :=
    fun τ a b h1 h2 => le_trans (by nlinarith) (hgap τ a b h1 h2)
  have hbar' : ∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 →
      C1 * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ b : ℝ) - la τ a :=
    fun τ a b h1 h2 => le_trans (by nlinarith) (hbar τ a b h1 h2)
  obtain ⟨ρ, c, F0, ψ, φ, h, hρ, hρR, hc, hcb, hfin, hF0s, hF01, hF00, hF0n, hψm, hψB, hψΓ, hψ0,
    hφeq, hφs, hφl, hφmono, hhm, hdb, hhint, hsup, hpoleψ, hpoleφ⟩ :=
    hW E r X la x hp0 hp0r ho hgap' hbar' hinj
  set bb : ℝ := 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1 with hbbdef
  have hbb0 : 0 ≤ bb := by positivity
  have hO := ExF.isOpen_OmF X x
  have hOm : MeasurableSet (OmF X x) := hO.measurableSet
  set A : ℝ≥0∞ := ENNReal.ofReal (Real.exp (C1 * S)) * muF X x (Metric.ball 0 ρ ∩ OmF X x) with hAdef
  have hμρ : muF X x (Metric.ball 0 ρ ∩ OmF X x) ≤
      muF X x (Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x) :=
    measure_mono (Set.inter_subset_inter_left _ (Metric.ball_subset_ball hρR))
  have hA : A < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hμρ.trans_lt hfin)
  obtain ⟨F, hFd, hFI⟩ := GlobalTheory.T.plurisubharmonic_decreasing_limit_extension hO (eF X x) (IW.eF_smooth X x ho) (IW.eF_levi X x ho)
    (IW.eF_compact X x ho) φ hφs hφl hφmono F0 hF0s h hhm hdb A hhint

  have hexpφ : ∀ k, ∀ z ∈ OmF X x, Real.exp (-φ k z) = Real.exp (-phla X la (cpt X x z)) *
      Real.exp (bb * rhF X x z) * densF X x z * Real.exp (-ψ k (cpt X x z)) := by
    intro k z hz
    rw [hφeq k z hz]
    have hd := IW.densF_pos X x hz
    rw [show -(phla X la (cpt X x z) - bb * rhF X x z - Real.log (densF X x z) + ψ k (cpt X x z)) =
      -phla X la (cpt X x z) + bb * rhF X x z + Real.log (densF X x z) + -ψ k (cpt X x z) by ring,
      Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hd]
  have hE0 : ∀ z ∈ OmF X x, Real.exp (-phla X la (cpt X x z)) * Real.exp (bb * rhF X x z) *
      densF X x z ≤ Real.exp (-φ 0 z) := by
    intro z hz
    rw [hexpφ 0 z hz]
    have h1 : 1 ≤ Real.exp (-ψ 0 (cpt X x z)) := Real.one_le_exp (by linarith [hψ0 0 (cpt X x z)])
    have h0 : 0 ≤ Real.exp (-phla X la (cpt X x z)) * Real.exp (bb * rhF X x z) * densF X x z :=
      mul_nonneg (by positivity) (IW.densF_pos X x hz).le
    nlinarith

  have hball2 : Metric.ball (0 : V (nd X)) (ρ / 2) ⊆ OmF X x := fun z hz =>
    hcb (Metric.mem_closedBall.2 (le_trans (Metric.mem_ball.1 hz).le (by linarith)))
  have hu : DifferentiableOn ℂ (fun z => F0 z - F z) (Metric.ball 0 (ρ / 2)) := by
    have e : Set.EqOn (fun z => 1 - F z) (fun z => F0 z - F z) (Metric.ball 0 (ρ / 2)) := by
      intro z hz
      have hz' : ‖z‖ ≤ ρ / 2 := by
        have := (Metric.mem_ball.1 hz).le
        rwa [dist_zero_right] at this
      show 1 - F z = F0 z - F z
      rw [hF01 z hz']
    exact ((differentiableOn_const (1 : ℂ)).sub (hFd.mono hball2)).congr e.symm
  have hint0 : ∫⁻ z in Metric.ball (0 : V (nd X)) (ρ / 2),
      ENNReal.ofReal (‖F0 z - F z‖ ^ 2 * ‖z‖ ^ (-(2 * (nd X : ℝ)))) < ⊤ := by
    have hpt : ∀ z ∈ Metric.ball (0 : V (nd X)) (ρ / 2),
        ENNReal.ofReal (‖F0 z - F z‖ ^ 2 * ‖z‖ ^ (-(2 * (nd X : ℝ)))) ≤
          ENNReal.ofReal c⁻¹ * (ENNReal.ofReal (‖F0 z - F z‖ ^ 2) *
            ⨆ k, ENNReal.ofReal (Real.exp (-φ k z))) := by
      intro z hz
      have hp := hpoleφ z hz
      rw [ENNReal.ofReal_mul hc.le] at hp
      have hcc : ENNReal.ofReal c⁻¹ * ENNReal.ofReal c = 1 := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), inv_mul_cancel₀ hc.ne', ENNReal.ofReal_one]
      have ht : ENNReal.ofReal (‖z‖ ^ (-(2 * (nd X : ℝ)))) ≤
          ENNReal.ofReal c⁻¹ * ⨆ k, ENNReal.ofReal (Real.exp (-φ k z)) := by
        calc ENNReal.ofReal (‖z‖ ^ (-(2 * (nd X : ℝ))))
            = ENNReal.ofReal c⁻¹ * (ENNReal.ofReal c * ENNReal.ofReal (‖z‖ ^ (-(2 * (nd X : ℝ))))) := by
              rw [← mul_assoc, hcc, one_mul]
          _ ≤ _ := by gcongr
      rw [ENNReal.ofReal_mul (sq_nonneg _)]
      calc ENNReal.ofReal (‖F0 z - F z‖ ^ 2) * ENNReal.ofReal (‖z‖ ^ (-(2 * (nd X : ℝ))))
          ≤ ENNReal.ofReal (‖F0 z - F z‖ ^ 2) * (ENNReal.ofReal c⁻¹ *
              ⨆ k, ENNReal.ofReal (Real.exp (-φ k z))) := by gcongr
        _ = _ := by ring
    calc ∫⁻ z in Metric.ball (0 : V (nd X)) (ρ / 2),
          ENNReal.ofReal (‖F0 z - F z‖ ^ 2 * ‖z‖ ^ (-(2 * (nd X : ℝ))))
        ≤ ∫⁻ z in Metric.ball (0 : V (nd X)) (ρ / 2), ENNReal.ofReal c⁻¹ *
            (ENNReal.ofReal (‖F0 z - F z‖ ^ 2) * ⨆ k, ENNReal.ofReal (Real.exp (-φ k z))) :=
          setLIntegral_mono' Metric.isOpen_ball.measurableSet hpt
      _ = ENNReal.ofReal c⁻¹ * ∫⁻ z in Metric.ball (0 : V (nd X)) (ρ / 2),
            ENNReal.ofReal (‖F0 z - F z‖ ^ 2) * ⨆ k, ENNReal.ofReal (Real.exp (-φ k z)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal c⁻¹ * A := by
          gcongr
          exact (lintegral_mono_set hball2).trans hFI
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hA
  have hF0val : F 0 = 1 := by
    have h0 := GlobalTheory.T.holomorphic_weighted_square_integrable_vanishes hnd (fun z => F0 z - F z) (ρ / 2) (by linarith) hu hint0
    have h1 := hF01 0 (by rw [norm_zero]; linarith)
    rw [h1] at h0
    exact (sub_eq_zero.1 h0).symm

  have hmuF : muF X x = (volume.restrict (OmF X x)).withDensity
      (fun z => ENNReal.ofReal (densF X x z)) := rfl
  have hdm : Measurable fun z => ENNReal.ofReal (densF X x z) :=
    ENNReal.measurable_ofReal.comp (IW.densF_meas X x)
  have hrw : ∀ g : V (nd X) → ℝ≥0∞, ∫⁻ z, g z ∂muF X x =
      ∫⁻ z in OmF X x, ENNReal.ofReal (densF X x z) * g z := by
    intro g
    rw [hmuF, lintegral_withDensity_eq_lintegral_mul_non_measurable _ hdm
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    rfl
  have hWdom : ∀ z ∈ OmF X x, IW.Wpsi X la (fun _ => 0) (cpt X x z) =
      ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) := by
    intro z hz
    have hz' : cpt X x z ∈ X.dom := hz
    simp [IW.Wpsi, hz']
  have hka : ∀ z, ‖F z‖ ^ 2 / kaF X x bb z = ‖F z‖ ^ 2 * Real.exp (bb * rhF X x z) := by
    intro z
    rw [kaF, div_eq_mul_inv, ← Real.exp_neg]
    ring_nf
  have hval : ∀ z ∈ OmF X x, ENNReal.ofReal (densF X x z) *
      (ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x bb z) * IW.Wpsi X la (fun _ => 0) (cpt X x z)) =
      ENNReal.ofReal (‖F z‖ ^ 2 * (Real.exp (-phla X la (cpt X x z)) * Real.exp (bb * rhF X x z) *
        densF X x z)) := by
    intro z hz
    have hd := (IW.densF_pos X x hz).le
    rw [hWdom z hz, hka z, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hd]
    congr 1
    ring

  have hmain : ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x bb z) *
      IW.Wpsi X la (fun _ => 0) (cpt X x z) ∂muF X x ≤
      ENNReal.ofReal (Real.exp ((C1 + 2) * S)) *
        muF X x (Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x) := by
    rw [hrw]
    have hpt : ∀ z ∈ OmF X x, ENNReal.ofReal (densF X x z) *
        (ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x bb z) * IW.Wpsi X la (fun _ => 0) (cpt X x z)) ≤
        (Metric.ball (0 : V (nd X)) ρ).indicator
          (fun z => ENNReal.ofReal (2 * Real.exp (C1 * S)) * ENNReal.ofReal (densF X x z)) z +
        2 * (ENNReal.ofReal (‖F0 z - F z‖ ^ 2) * ⨆ k, ENNReal.ofReal (Real.exp (-φ k z))) := by
      intro z hz
      rw [hval z hz]
      set E0 := Real.exp (-phla X la (cpt X x z)) * Real.exp (bb * rhF X x z) * densF X x z
        with hE0def
      have hE0n : 0 ≤ E0 := mul_nonneg (by positivity) (IW.densF_pos X x hz).le
      have hsq := HE.sq_le_two (F0 z) (F z)
      calc ENNReal.ofReal (‖F z‖ ^ 2 * E0)
          ≤ ENNReal.ofReal (2 * ‖F0 z‖ ^ 2 * E0 + 2 * (‖F0 z - F z‖ ^ 2 * E0)) := by
            apply ENNReal.ofReal_le_ofReal
            nlinarith
        _ = ENNReal.ofReal (2 * ‖F0 z‖ ^ 2 * E0) + 2 * ENNReal.ofReal (‖F0 z - F z‖ ^ 2 * E0) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (p := (2 : ℝ)) (q := ‖F0 z - F z‖ ^ 2 * E0) (by norm_num), ENNReal.ofReal_ofNat]
        _ ≤ _ := by
            gcongr
            · by_cases hzb : z ∈ Metric.ball (0 : V (nd X)) ρ
              · rw [Set.indicator_of_mem hzb, ← ENNReal.ofReal_mul (by positivity)]
                apply ENNReal.ofReal_le_ofReal
                have h1 : ‖F0 z‖ ^ 2 ≤ 1 := by
                  have := hF0n z
                  nlinarith [norm_nonneg (F0 z)]
                have h2 : E0 ≤ Real.exp (C1 * S) * densF X x z := by
                  rw [hE0def]
                  exact mul_le_mul_of_nonneg_right (hsup z hzb) (IW.densF_pos X x hz).le
                have h3 : 0 ≤ Real.exp (C1 * S) * densF X x z :=
                  mul_nonneg (Real.exp_pos _).le (IW.densF_pos X x hz).le
                nlinarith [sq_nonneg ‖F0 z‖]
              · have hz0 : F0 z = 0 := hF00 z (by
                  rw [Metric.mem_ball, dist_zero_right, not_lt] at hzb
                  exact hzb)
                simp [hz0]
            · rw [ENNReal.ofReal_mul (sq_nonneg _)]
              gcongr
              refine le_trans ?_ (le_iSup _ 0)
              exact ENNReal.ofReal_le_ofReal (hE0 z hz)
    calc ∫⁻ z in OmF X x, ENNReal.ofReal (densF X x z) *
          (ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x bb z) * IW.Wpsi X la (fun _ => 0) (cpt X x z))
        ≤ ∫⁻ z in OmF X x, ((Metric.ball (0 : V (nd X)) ρ).indicator
            (fun z => ENNReal.ofReal (2 * Real.exp (C1 * S)) * ENNReal.ofReal (densF X x z)) z +
          2 * (ENNReal.ofReal (‖F0 z - F z‖ ^ 2) * ⨆ k, ENNReal.ofReal (Real.exp (-φ k z)))) :=
          setLIntegral_mono' hOm hpt
      _ = (∫⁻ z in OmF X x, (Metric.ball (0 : V (nd X)) ρ).indicator
            (fun z => ENNReal.ofReal (2 * Real.exp (C1 * S)) * ENNReal.ofReal (densF X x z)) z) +
          2 * ∫⁻ z in OmF X x, ENNReal.ofReal (‖F0 z - F z‖ ^ 2) *
            ⨆ k, ENNReal.ofReal (Real.exp (-φ k z)) := by
          rw [lintegral_add_left ((Measurable.const_mul hdm _).indicator Metric.isOpen_ball.measurableSet),
            lintegral_const_mul' _ _ (by norm_num)]
      _ ≤ ENNReal.ofReal (2 * Real.exp (C1 * S)) * muF X x (Metric.ball 0 ρ ∩ OmF X x) + 2 * A := by
          gcongr
          rw [lintegral_indicator Metric.isOpen_ball.measurableSet,
            lintegral_const_mul _ hdm, hmuF, withDensity_apply _
              (Metric.isOpen_ball.measurableSet.inter hOm),
            Measure.restrict_restrict Metric.isOpen_ball.measurableSet,
            Measure.restrict_restrict (Metric.isOpen_ball.measurableSet.inter hOm),
            Set.inter_assoc, Set.inter_self]
      _ = ENNReal.ofReal (4 * Real.exp (C1 * S)) * muF X x (Metric.ball 0 ρ ∩ OmF X x) := by
          rw [hAdef, show (4 : ℝ) * Real.exp (C1 * S) = 2 * Real.exp (C1 * S) + 2 * Real.exp (C1 * S)
            by ring, ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_ofNat]
          ring
      _ ≤ _ := by
          gcongr
          have hS' : 2 ≤ S + 1 := by linarith
          have h4 : (4 : ℝ) ≤ Real.exp (2 * S) := by
            have h1 : S + 1 ≤ Real.exp S := Real.add_one_le_exp S
            have h2 : Real.exp (2 * S) = Real.exp S * Real.exp S := by
              rw [← Real.exp_add]; ring_nf
            nlinarith
          rw [show (C1 + 2) * S = C1 * S + 2 * S by ring, Real.exp_add]
          nlinarith [Real.exp_pos (C1 * S)]
  have hfinI : ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x bb z) *
      IW.Wpsi X la (fun _ => 0) (cpt X x z) ∂muF X x < ⊤ :=
    hmain.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)

  have hac : muF X x ≪ volume.restrict (OmF X x) := by
    rw [hmuF]; exact withDensity_absolutelyContinuous _ _
  have hae : ∀ᵐ z ∂muF X x, z ∈ OmF X x := hac.ae_le (ae_restrict_mem hOm)
  have hext : ∀ C : Set (Frame X.Ψ r), IsCompact C → C ⊆ X.dom →
      ∫⁻ z in sat X x C, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x z))) ∂muF X x < ⊤ := by
    intro C _ _
    refine lt_of_le_of_lt (setLIntegral_le_lintegral _ _) (lt_of_le_of_lt ?_ hfinI)
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with z hz
    rw [hWdom z hz, hka z, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h1 : 1 ≤ Real.exp (bb * rhF X x z) :=
      Real.one_le_exp (mul_nonneg hbb0 (ExF.rhF_nonneg X x ho hz))
    have h2 : 0 ≤ ‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x z)) := by positivity
    nlinarith
  obtain ⟨P0, hBE, hPF⟩ := extFStatement_holds r X x ho la F hFd hext

  set Ψw : Frame X.Ψ r → ℝ≥0∞ := fun y => ⨆ k, ENNReal.ofReal (Real.exp (-ψ k y)) with hΨdef
  have hΨm : Measurable Ψw :=
    Measurable.iSup fun k => ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hψm k).neg)
  have hΨB : ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Ψw (rmul y b) = Ψw y := by
    intro y hy b hb
    simp only [hΨdef, hψB _ y hy b hb]
  have hΨΓ : ∀ γ ∈ X.Γ, ∀ y ∈ X.dom, Ψw (lact γ y) = Ψw y := by
    intro γ hγ y hy
    simp only [hΨdef, hψΓ _ γ hγ y hy]
  have hF0R : ∀ z, 1 / (100 * (r : ℝ) ^ 2) < ‖z‖ → F0 z = 0 := fun z hz =>
    hF00 z (hρR.trans hz.le)
  have hintT : ∫⁻ z, ENNReal.ofReal (‖F0 z - F z‖ ^ 2 * Real.exp (-phla X la (cpt X x z))) *
      Ψw (cpt X x z) ∂muF X x < ⊤ := by
    rw [hrw]
    refine lt_of_le_of_lt ?_ hA
    refine le_trans (setLIntegral_mono' hOm fun z hz => ?_) hFI
    have hd := (IW.densF_pos X x hz).le
    simp only [hΨdef]
    rw [ENNReal.mul_iSup, ENNReal.mul_iSup, ENNReal.mul_iSup]
    refine iSup_mono fun k => ?_
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hd,
      ← ENNReal.ofReal_mul (sq_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    rw [hexpφ k z hz]
    have h1 : 1 ≤ Real.exp (bb * rhF X x z) :=
      Real.one_le_exp (mul_nonneg hbb0 (ExF.rhF_nonneg X x ho hz))
    have h2 : 0 ≤ ‖F0 z - F z‖ ^ 2 * Real.exp (-phla X la (cpt X x z)) * densF X x z *
      Real.exp (-ψ k (cpt X x z)) := by positivity
    nlinarith
  refine ⟨F, P0, hFd, hBE, hPF, ?_, ?_, hfinI, hmain⟩
  · have h0 := hPF 0 (IW.zero_mem_OmF X x ho)
    rw [IW.cpt_zero] at h0
    rw [h0, hF0val]
  · intro γ hγ hne
    exact GlobalTheory.T.peakExtension_vanish_other_orbit_points X la x ho hnd Ψw hΨm hΨB hΨΓ c (ρ / 2) hc (by linarith) hpoleψ hinj F0 F hF0R hFd
      hintT P0 hBE hPF γ hγ hne

end GlobalTheory.HormanderPeak
