import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

private theorem le_of_subMeanValue_log_sq_le_on_annulus_boundary (g : ℂ → ℝ) (R r0 ε δ M : ℝ) (hr0 : 0 < r0) (hR : r0 < R) (hε : 0 ≤ ε)
    (hδ : 0 < δ) (husc : UpperSemicontinuousOn g {ζ : ℂ | r0 ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ R})
    (hsub : ∀ (c : ℂ) (s : ℝ), 0 < s → r0 < ‖c‖ - s → ‖c‖ + s < R →
      CircleIntegrable g c s ∧ g c ≤ Real.circleAverage g c s)
    (hin : ∀ ζ : ℂ, ‖ζ‖ = r0 → g ζ + ε * Real.log ‖ζ‖ + δ * ‖ζ‖ ^ 2 ≤ M)
    (hout : ∀ ζ : ℂ, ‖ζ‖ = R → g ζ + ε * Real.log ‖ζ‖ + δ * ‖ζ‖ ^ 2 ≤ M) :
    ∀ ζ : ℂ, r0 ≤ ‖ζ‖ → ‖ζ‖ ≤ R → g ζ + ε * Real.log ‖ζ‖ + δ * ‖ζ‖ ^ 2 ≤ M := by
  set A : Set ℂ := {ζ : ℂ | r0 ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ R} with hA
  have hAc : IsCompact A := by
    apply (ProperSpace.isCompact_closedBall (0 : ℂ) R).of_isClosed_subset
    · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
    · intro z hz
      simpa using hz.2
  have hAne : A.Nonempty := ⟨(R : ℂ), by
    simp only [hA, Set.mem_setOf_eq, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (hr0.trans hR)]
    exact ⟨hR.le, le_rfl⟩⟩
  have hcont : ContinuousOn (fun ζ : ℂ => ε * Real.log ‖ζ‖ + δ * ‖ζ‖ ^ 2) A := by
    intro z hz
    have hz0 : ‖z‖ ≠ 0 := (hr0.trans_le hz.1).ne'
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.add
    · exact continuousAt_const.mul (Real.continuousAt_log hz0 |>.comp continuous_norm.continuousAt)
    · exact continuousAt_const.mul (continuous_norm.continuousAt.pow 2)
  have husck : UpperSemicontinuousOn (fun ζ : ℂ => g ζ + (ε * Real.log ‖ζ‖ + δ * ‖ζ‖ ^ 2)) A :=
    husc.add hcont.upperSemicontinuousOn
  obtain ⟨z0, hz0A, hmax⟩ := husck.exists_isMaxOn hAne hAc
  have key : g z0 + (ε * Real.log ‖z0‖ + δ * ‖z0‖ ^ 2) ≤ M := by
    rcases eq_or_lt_of_le hz0A.1 with h1 | h1
    · have := hin z0 h1.symm
      linarith
    rcases eq_or_lt_of_le hz0A.2 with h2 | h2
    · have := hout z0 h2
      linarith
    exfalso
    set s := min (‖z0‖ - r0) (R - ‖z0‖) / 2 with hs
    have hs0 : 0 < s := by
      have : 0 < min (‖z0‖ - r0) (R - ‖z0‖) := lt_min (by linarith) (by linarith)
      linarith
    have hs1 : s < ‖z0‖ - r0 := by
      have := min_le_left (‖z0‖ - r0) (R - ‖z0‖)
      linarith
    have hs2 : s < R - ‖z0‖ := by
      have := min_le_right (‖z0‖ - r0) (R - ‖z0‖)
      linarith
    obtain ⟨hgi, hgle⟩ := hsub z0 s hs0 (by linarith) (by linarith)
    have hsph : Metric.sphere z0 s ⊆ A := by
      intro x hx
      rw [mem_sphere_iff_norm] at hx
      have h3 : ‖x‖ ≤ ‖z0‖ + ‖x - z0‖ := by
        have := norm_add_le z0 (x - z0)
        simpa using this
      have h4 : ‖z0‖ ≤ ‖x‖ + ‖x - z0‖ := by
        have := norm_sub_le x (x - z0)
        simpa using this
      exact ⟨by linarith, by linarith⟩
    have hci2 : CircleIntegrable (fun ζ : ℂ => ε * Real.log ‖ζ‖ + δ * ‖ζ‖ ^ 2) z0 s :=
      ContinuousOn.circleIntegrable hs0.le (hcont.mono hsph)
    have hlogc : CircleIntegrable (fun ζ : ℂ => ε * Real.log ‖ζ‖) z0 s :=
      ContinuousOn.circleIntegrable hs0.le (by
        intro z hz
        have hz0 : ‖z‖ ≠ 0 := (hr0.trans_le (hsph hz).1).ne'
        exact (continuousAt_const.mul (Real.continuousAt_log hz0 |>.comp continuous_norm.continuousAt)).continuousWithinAt)
    have hsqc : CircleIntegrable (fun ζ : ℂ => δ * ‖ζ‖ ^ 2) z0 s :=
      ContinuousOn.circleIntegrable hs0.le (by fun_prop)
    have havg_le : Real.circleAverage (fun ζ : ℂ => g ζ + (ε * Real.log ‖ζ‖ + δ * ‖ζ‖ ^ 2)) z0 s ≤
        g z0 + (ε * Real.log ‖z0‖ + δ * ‖z0‖ ^ 2) := by
      apply Real.circleAverage_mono_on_of_le_circle (hgi.add hci2)
      intro x hx
      rw [abs_of_pos hs0] at hx
      exact hmax (hsph hx)
    have hsplit : Real.circleAverage (fun ζ : ℂ => g ζ + (ε * Real.log ‖ζ‖ + δ * ‖ζ‖ ^ 2)) z0 s =
        Real.circleAverage g z0 s + (ε * Real.circleAverage (fun ζ : ℂ => Real.log ‖ζ‖) z0 s +
          δ * Real.circleAverage (fun ζ : ℂ => ‖ζ‖ ^ 2) z0 s) := by
      rw [Real.circleAverage_fun_add hgi hci2, Real.circleAverage_fun_add hlogc hsqc,
        ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.cA_mul, ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.cA_mul]
    have hlog : Real.log ‖z0‖ ≤ Real.circleAverage (fun ζ : ℂ => Real.log ‖ζ‖) z0 s := by
      have h := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := 0) (c := z0) hs0.ne'
      simp only [sub_zero] at h
      rw [h]
      have hz0pos : 0 < ‖z0‖ := by linarith
      have hl : Real.log (s⁻¹ * ‖z0‖) ≤ (s⁻¹ * ‖z0‖).posLog := by
        unfold Real.posLog
        exact le_max_right _ _
      rw [Real.log_mul (inv_ne_zero hs0.ne') hz0pos.ne', Real.log_inv] at hl
      linarith
    have hsq : Real.circleAverage (fun ζ : ℂ => ‖ζ‖ ^ 2) z0 s = ‖z0‖ ^ 2 + s ^ 2 := by
      have h := ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.circleAverage_norm_sub_sq z0 0 hs0.le
      simpa using h
    rw [hsplit, hsq] at havg_le
    have h5 : ε * Real.log ‖z0‖ ≤ ε * Real.circleAverage (fun ζ : ℂ => Real.log ‖ζ‖) z0 s :=
      mul_le_mul_of_nonneg_left hlog hε
    have h6 : 0 < δ * s ^ 2 := mul_pos hδ (pow_pos hs0 2)
    nlinarith
  intro ζ h1 h2
  have := hmax (show ζ ∈ A from ⟨h1, h2⟩)
  simp only [Set.mem_setOf_eq] at this
  linarith

private theorem le_add_two_of_subMeanValue_loglog_bound (g : ℂ → ℝ) (R B K A : ℝ) (hR : 0 < R) (hK : 0 ≤ K) (hA : 1 ≤ A)
    (husc : UpperSemicontinuousOn g {ζ : ℂ | 0 < ‖ζ‖ ∧ ‖ζ‖ ≤ R})
    (hsub : ∀ (c : ℂ) (s : ℝ), 0 < s → 0 < ‖c‖ - s → ‖c‖ + s < R →
      CircleIntegrable g c s ∧ g c ≤ Real.circleAverage g c s)
    (hgrow : ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ ≤ R → g ζ ≤ K * (1 + Real.log (A + |Real.log ‖ζ‖|)))
    (hout : ∀ ζ : ℂ, ‖ζ‖ = R → g ζ ≤ B) :
    ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ ≤ R → g ζ ≤ B + 2 := by
  intro ζ0 hζ0 hζ0R
  rcases eq_or_lt_of_le hζ0R with hEq | hlt
  · have := hout ζ0 hEq
    linarith
  have hLpos : 0 < Real.log (R / ‖ζ0‖) := Real.log_pos (by rw [lt_div_iff₀ hζ0]; linarith)
  set ε : ℝ := 1 / (Real.log (R / ‖ζ0‖) + 1) with hεdef
  have hε : 0 < ε := by positivity
  set δ : ℝ := 1 / (R ^ 2 + 1) with hδdef
  have hδ : 0 < δ := by positivity
  set et : ℝ := ε / (2 * (K + 1)) with hetdef
  have het : 0 < et := by positivity
  have hKet : K * et ≤ ε / 2 := by
    rw [hetdef, mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set c0 : ℝ := K + ε * A / 2 - K * (1 + Real.log et) with hc0
  set x : ℝ := max (max 0 (1 - Real.log ‖ζ0‖)) (2 * (c0 - B - ε * Real.log R) / ε) with hxdef
  have hx0 : 0 ≤ x := le_trans (le_max_left _ _) (le_max_left _ _)
  have hx1 : 1 - Real.log ‖ζ0‖ ≤ x := le_trans (le_max_right _ _) (le_max_left _ _)
  have hx2 : 2 * (c0 - B - ε * Real.log R) / ε ≤ x := le_max_right _ _
  set r0 : ℝ := Real.exp (-x) with hr0def
  have hr0 : 0 < r0 := Real.exp_pos _
  have hlogr0 : Real.log r0 = -x := Real.log_exp _
  have hr0lt : r0 < ‖ζ0‖ := by
    rw [← Real.exp_log hζ0, hr0def, Real.exp_lt_exp]
    linarith
  have hmain := le_of_subMeanValue_log_sq_le_on_annulus_boundary g R r0 ε δ (B + ε * Real.log R + δ * R ^ 2) hr0 (hr0lt.trans hlt) hε.le hδ
    (husc.mono (fun z hz => ⟨hr0.trans_le hz.1, hz.2⟩))
    (fun c s hs h1 h2 => hsub c s hs (by linarith) h2)
    (by
      intro ζ hζ
      have hg := hgrow ζ (by rw [hζ]; exact hr0) (by rw [hζ]; linarith)
      rw [hζ, hlogr0, abs_neg, abs_of_nonneg hx0] at hg
      rw [hζ, hlogr0]
      have hAx : 0 < A + x := by linarith
      have hl1 : Real.log (et * (A + x)) ≤ et * (A + x) - 1 := Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_mul het.ne' hAx.ne'] at hl1
      have hl2 : K * Real.log (A + x) ≤ K * (et * (A + x) - 1 - Real.log et) :=
        mul_le_mul_of_nonneg_left (by linarith) hK
      have hl3 : K * et * (A + x) ≤ ε / 2 * (A + x) := mul_le_mul_of_nonneg_right hKet hAx.le
      have hl4 : 2 * (c0 - B - ε * Real.log R) ≤ ε * x := by
        have := mul_le_mul_of_nonneg_left hx2 hε.le
        have e : ε * (2 * (c0 - B - ε * Real.log R) / ε) = 2 * (c0 - B - ε * Real.log R) := by
          field_simp
        linarith
      have hr0R : r0 ^ 2 ≤ R ^ 2 := by
        have : r0 ≤ R := (hr0lt.trans hlt).le
        nlinarith
      have hl5 : δ * r0 ^ 2 ≤ δ * R ^ 2 := mul_le_mul_of_nonneg_left hr0R hδ.le
      rw [hc0] at hl4
      nlinarith)
    (by
      intro ζ hζ
      have := hout ζ hζ
      rw [hζ]
      linarith)
    ζ0 hr0lt.le hζ0R
  have hεL : ε * (Real.log R - Real.log ‖ζ0‖) ≤ 1 := by
    rw [← Real.log_div hR.ne' hζ0.ne', hεdef]
    rw [div_mul_eq_mul_div, _root_.one_mul, div_le_one (by positivity)]
    linarith
  have hδR : δ * R ^ 2 ≤ 1 := by
    rw [hδdef, div_mul_eq_mul_div, _root_.one_mul, div_le_one (by positivity)]
    linarith
  have hsq : 0 ≤ δ * ‖ζ0‖ ^ 2 := by positivity
  nlinarith

theorem LevelTowerAlt.psh_log_growth_bounded : ∀ (n a : ℕ) (ρ C : ℝ) (u : (Fin n → ℂ) → ℝ), 0 < ρ → ρ ≤ 1 → ReciprocityTheory.AnForm.A.IsPsh (Flat.punct n a ρ) u → (∀ t ∈ Flat.punct n a ρ, u t ≤ C * (1 + Real.log (Flat.logSize a t))) → ∃ C' : ℝ, ∀ t ∈ Flat.punct n a (ρ / 2), u t ≤ C' := by
  intro n a ρ C u hρ hρ1 hpsh hgrow
  classical
  set K : ℝ := max C 0 with hKdef
  have hK : 0 ≤ K := le_max_right _ _
  set R : ℝ := 3 * ρ / 4 with hRdef
  have hR : 0 < R := by positivity
  have hRρ : R < ρ := by linarith
  have hWsub : ∀ z : Fin n → ℂ, (∀ j, ‖z j‖ ≤ R) → (∀ j : Fin n, (j : ℕ) < a → z j ≠ 0) →
      z ∈ Flat.punct n a ρ := by
    intro z h1 h2
    refine ⟨?_, h2⟩
    rw [mem_ball_zero_iff]
    exact lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg hR.le).2 h1) hRρ
  have hls1 : ∀ z : Fin n → ℂ, 1 ≤ Flat.logSize a z := by
    intro z
    unfold Flat.logSize
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hgK : ∀ z ∈ Flat.punct n a ρ, u z ≤ K * (1 + Real.log (Flat.logSize a z)) := by
    intro z hz
    have h := hgrow z hz
    have hl : 0 ≤ 1 + Real.log (Flat.logSize a z) := by
      have := Real.log_nonneg (hls1 z)
      linarith
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hl)
  set B0 : ℝ := K * (1 + Real.log (1 + n * |Real.log R|)) with hB0
  have main : ∀ k : ℕ, ∀ z : Fin n → ℂ, (∀ j, ‖z j‖ ≤ R) → (∀ j : Fin n, (j : ℕ) < a → z j ≠ 0) →
      (Finset.univ.filter (fun i : Fin n => (i : ℕ) < a ∧ ‖z i‖ ≠ R)).card ≤ k →
      u z ≤ B0 + 2 * (k : ℝ) := by
    intro k
    induction k with
    | zero =>
      intro z h1 h2 hb
      have hz := hWsub z h1 h2
      have hall : ∀ j : Fin n, (j : ℕ) < a → ‖z j‖ = R := by
        intro j hj
        by_contra hne
        have hm : j ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < a ∧ ‖z i‖ ≠ R) := by
          simp [hj, hne]
        have := Finset.card_pos.2 ⟨j, hm⟩
        omega
      have hls : Flat.logSize a z ≤ 1 + n * |Real.log R| := by
        unfold Flat.logSize
        rw [Finset.sum_congr rfl (g := fun _ => |Real.log R|)
          (fun i hi => by rw [hall i (Finset.mem_filter.1 hi).2])]
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
      have hu := hgK z hz
      have hlog : Real.log (Flat.logSize a z) ≤ Real.log (1 + n * |Real.log R|) :=
        Real.log_le_log (by linarith [hls1 z]) hls
      have := mul_le_mul_of_nonneg_left (show 1 + Real.log (Flat.logSize a z) ≤
        1 + Real.log (1 + n * |Real.log R|) by linarith) hK
      push_cast
      linarith
    | succ k ih =>
      intro z h1 h2 hb
      by_cases hbk : (Finset.univ.filter (fun i : Fin n => (i : ℕ) < a ∧ ‖z i‖ ≠ R)).card ≤ k
      · have := ih z h1 h2 hbk
        push_cast
        linarith
      have hpos : 0 < (Finset.univ.filter (fun i : Fin n => (i : ℕ) < a ∧ ‖z i‖ ≠ R)).card := by omega
      obtain ⟨j, hj⟩ := Finset.card_pos.1 hpos
      have hj' := (Finset.mem_filter.1 hj).2
      have hjz0 : 0 < ‖z j‖ := norm_pos_iff.2 (h2 j hj'.1)
      have hupdW1 : ∀ ζ : ℂ, ‖ζ‖ ≤ R → ∀ i, ‖Function.update z j ζ i‖ ≤ R := by
        intro ζ hζ i
        by_cases h : i = j
        · subst h
          rw [Function.update_self]
          exact hζ
        · rw [Function.update_of_ne h]
          exact h1 i
      have hupdW2 : ∀ ζ : ℂ, ζ ≠ 0 → ∀ i : Fin n, (i : ℕ) < a → Function.update z j ζ i ≠ 0 := by
        intro ζ hζ i hi
        by_cases h : i = j
        · subst h
          rw [Function.update_self]
          exact hζ
        · rw [Function.update_of_ne h]
          exact h2 i hi
      have hjmem : j ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < a) := by simp [hj'.1]
      have key := le_add_two_of_subMeanValue_loglog_bound (fun ζ => u (Function.update z j ζ)) R (B0 + 2 * (k : ℝ)) K
        (Flat.logSize a z) hR hK (hls1 z)
        (by
          intro ζ hζ y hy
          have hmem : Function.update z j ζ ∈ Flat.punct n a ρ :=
            hWsub _ (hupdW1 ζ hζ.2) (hupdW2 ζ (norm_pos_iff.1 hζ.1))
          have hu := hpsh.1 (Function.update z j ζ) hmem y hy
          have hcont : Continuous (fun ξ : ℂ => Function.update z j ξ) :=
            continuous_const.update j continuous_id
          have ht : Filter.Tendsto (fun ξ : ℂ => Function.update z j ξ)
              (𝓝[{ζ : ℂ | 0 < ‖ζ‖ ∧ ‖ζ‖ ≤ R}] ζ) (𝓝[Flat.punct n a ρ] (Function.update z j ζ)) :=
            tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
              (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
              (eventually_nhdsWithin_of_forall (fun ξ hξ =>
                hWsub _ (hupdW1 ξ hξ.2) (hupdW2 ξ (norm_pos_iff.1 hξ.1))))
          exact ht.eventually hu)
        (by
          intro c s hs h1' h2'
          have hupd : ∀ ξ : ℂ, Function.update z j c + ξ • Pi.single j (s : ℂ) =
              Function.update z j ((s : ℂ) * ξ + c) := by
            intro ξ
            ext i
            by_cases h : i = j
            · subst h
              rw [Pi.add_apply, Pi.smul_apply, Function.update_self, Function.update_self,
                Pi.single_eq_same, smul_eq_mul]
              ring
            · rw [Pi.add_apply, Pi.smul_apply, Function.update_of_ne h, Function.update_of_ne h,
                Pi.single_eq_of_ne h, smul_zero, add_zero]
          have hdisc : ∀ ξ : ℂ, ‖ξ‖ ≤ 1 →
              Function.update z j c + ξ • Pi.single j (s : ℂ) ∈ Flat.punct n a ρ := by
            intro ξ hξ
            rw [hupd]
            have hn1 : ‖(s : ℂ) * ξ‖ ≤ s := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
              nlinarith [norm_nonneg ξ]
            have hup : ‖(s : ℂ) * ξ + c‖ ≤ ‖c‖ + s := by
              have := norm_add_le ((s : ℂ) * ξ) c
              linarith
            have hlo : ‖c‖ - s ≤ ‖(s : ℂ) * ξ + c‖ := by
              have := norm_sub_le ((s : ℂ) * ξ + c) ((s : ℂ) * ξ)
              rw [add_sub_cancel_left] at this
              linarith
            exact hWsub _ (hupdW1 _ (by linarith)) (hupdW2 _ (by
              intro h0
              rw [h0, norm_zero] at hlo
              linarith))
          obtain ⟨hI, hle⟩ := hpsh.2 (Function.update z j c) (Pi.single j (s : ℂ)) hdisc
          have e : (fun θ : ℝ => u (Function.update z j (circleMap c s θ))) =
              (fun θ : ℝ => u (Function.update z j c + circleMap 0 1 θ • Pi.single j (s : ℂ))) := by
            funext θ
            rw [hupd]
            rw [show circleMap c s θ = (s : ℂ) * circleMap 0 1 θ + c by
              simp only [circleMap, Complex.ofReal_one]
              ring]
          refine ⟨?_, ?_⟩
          · unfold CircleIntegrable at hI ⊢
            rw [e]
            exact hI
          · rw [Real.circleAverage_eq_circleAverage_zero_one]
            have e2 : (fun ξ : ℂ => u (Function.update z j ((s : ℂ) * ξ + c))) =
                (fun ξ : ℂ => u (Function.update z j c + ξ • Pi.single j (s : ℂ))) := by
              funext ξ
              rw [hupd]
            rw [e2]
            exact hle)
        (by
          intro ζ hζ0 hζR
          have hmem := hWsub _ (hupdW1 ζ hζR) (hupdW2 ζ (norm_pos_iff.1 hζ0))
          have h := hgK _ hmem
          have hls : Flat.logSize a (Function.update z j ζ) ≤ Flat.logSize a z + |Real.log ‖ζ‖| := by
            unfold Flat.logSize
            have hterm : ∀ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < a),
                |Real.log ‖Function.update z j ζ i‖| ≤
                  |Real.log ‖z i‖| + (if i = j then |Real.log ‖ζ‖| else 0) := by
              intro i _
              by_cases hij : i = j
              · subst hij
                rw [Function.update_self, if_pos rfl]
                linarith [abs_nonneg (Real.log ‖z i‖)]
              · rw [Function.update_of_ne hij, if_neg hij]
                linarith
            have hsum := Finset.sum_le_sum hterm
            rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hjmem] at hsum
            linarith
          have hlog := Real.log_le_log (by linarith [hls1 (Function.update z j ζ)]) hls
          exact h.trans (mul_le_mul_of_nonneg_left (by linarith) hK))
        (by
          intro ζ hζ
          apply ih
          · exact hupdW1 ζ hζ.le
          · exact hupdW2 ζ (by
              intro h0
              rw [h0, norm_zero] at hζ
              linarith)
          · have hsub : Finset.univ.filter (fun i : Fin n => (i : ℕ) < a ∧ ‖Function.update z j ζ i‖ ≠ R) ⊆
                (Finset.univ.filter (fun i : Fin n => (i : ℕ) < a ∧ ‖z i‖ ≠ R)).erase j := by
              intro i hi
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
              by_cases h : i = j
              · subst h
                rw [Function.update_self] at hi
                exact absurd hζ hi.2
              · rw [Finset.mem_erase]
                refine ⟨h, ?_⟩
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                rw [Function.update_of_ne h] at hi
                exact hi
            have := Finset.card_le_card hsub
            rw [Finset.card_erase_of_mem hj] at this
            omega)
        (z j) hjz0 (h1 j)
      simp only [Function.update_eq_self] at key
      push_cast
      linarith
  refine ⟨B0 + 2 * (n : ℝ), ?_⟩
  intro t ht
  obtain ⟨htb, htnz⟩ := ht
  rw [mem_ball_zero_iff] at htb
  have h1 : ∀ j, ‖t j‖ ≤ R := fun j => ((norm_le_pi_norm t j).trans htb.le).trans (by linarith)
  exact main n t h1 htnz ((Finset.card_filter_le _ _).trans (by simp))
