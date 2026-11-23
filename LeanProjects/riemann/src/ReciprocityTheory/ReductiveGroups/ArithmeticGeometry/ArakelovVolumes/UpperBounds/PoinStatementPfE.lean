import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfD

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def idF (X : Data E r) : Frame X.Ψ r := fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)

theorem idF_mem (X : Data E r) : idF X ∈ Bor X.Ψ r := by
  simp only [Bor, Set.mem_setOf_eq]
  intro τ
  refine ⟨?_, fun a c h => ?_⟩
  · have h1 : mat (idF X) τ = 1 := by
      ext i j
      rfl
    rw [h1, Matrix.det_one]
    exact one_ne_zero
  · simp [idF, Matrix.one_apply, ne_of_gt h]

theorem rmul_idF (X : Data E r) (y : Frame X.Ψ r) : rmul y (idF X) = y := by
  funext τ
  show (mat y τ * mat (idF X) τ : Matrix (Fin r) (Fin r) ℂ) = y τ
  have h1 : mat (idF X) τ = 1 := by
    ext i j
    rfl
  rw [h1, mul_one]
  rfl

theorem bchar_idF (X : Data E r) (la : Wt X.Ψ r) : bchar la (idF X) = 1 := by
  simp [bchar, idF]

theorem bchar_contAt (X : Data E r) (la : Wt X.Ψ r) : ContinuousAt (bchar la) (idF X) := by
  unfold bchar
  refine tendsto_finset_prod _ fun τ _ => tendsto_finset_prod _ fun i _ => ?_
  have hc : Continuous fun b : Frame X.Ψ r => b τ i i := by fun_prop
  exact hc.continuousAt.zpow₀ _ (Or.inl (by simp [idF]))

theorem ball_int_bound (X : Data E r) (la : Wt X.Ψ r) {R0 ρ : ℝ}
    (hgood : ∀ w ∈ Metric.ball (0 : V (nd X)) R0, (∀ τ, (mat (nmat X w) τ).det ≠ 0) ∧
      (∀ τ, ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (lminor (Gw X w τ) i).re) ∧ 1 / 2 < nfw X la w)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (hxo : IsOrth X x) (P : Frame X.Ψ r → ℂ) :
    Metric.ball (0 : V (nd X)) (min R0 ρ) ⊆ Bset X x ρ ∧
      ∫⁻ z in Metric.ball (0 : V (nd X)) (min R0 ρ), ‖P (cpt X x z)‖ₑ ^ 2 ≤ ENNReal.ofReal 4 *
        ∫⁻ w in Bset X x ρ, ‖P (cpt X x w)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w))) := by
  have hgoodR := fun w (hw : w ∈ Metric.ball (0 : V (nd X)) (min R0 ρ)) =>
    hgood w (Metric.ball_subset_ball (min_le_left _ _) hw)
  have hmem : Metric.ball (0 : V (nd X)) (min R0 ρ) ⊆ Bset X x ρ := fun w hw => by
    obtain ⟨h1, h2, -⟩ := hgoodR w hw
    exact ⟨lt_of_lt_of_le (mem_ball_zero_iff.1 hw) (min_le_right _ _), cpt_mem_dom X hx hxo h1 h2⟩
  refine ⟨hmem, ?_⟩
  have hpt : ∀ w ∈ Metric.ball (0 : V (nd X)) (min R0 ρ), ‖P (cpt X x w)‖ₑ ^ 2 ≤ ENNReal.ofReal 4 *
      (‖P (cpt X x w)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w)))) := by
    intro w hw
    obtain ⟨-, -, h3⟩ := hgoodR w hw
    have hn : X.nfac la (cpt X x w) = nfw X la w := nfac_cpt_orth X la hxo w
    have he : 1 ≤ ENNReal.ofReal 4 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w))) := by
      rw [exp_neg_phla X la (by rw [hn]; linarith), hn, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by nlinarith)
    calc ‖P (cpt X x w)‖ₑ ^ 2 = ‖P (cpt X x w)‖ₑ ^ 2 * 1 := (mul_one _).symm
      _ ≤ ‖P (cpt X x w)‖ₑ ^ 2 *
          (ENNReal.ofReal 4 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w)))) := by gcongr
      _ = _ := by ring
  calc ∫⁻ z in Metric.ball (0 : V (nd X)) (min R0 ρ), ‖P (cpt X x z)‖ₑ ^ 2
      ≤ ∫⁻ z in Metric.ball (0 : V (nd X)) (min R0 ρ), ENNReal.ofReal 4 *
          (‖P (cpt X x z)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x z)))) :=
        setLIntegral_mono' Metric.isOpen_ball.measurableSet hpt
    _ = ENNReal.ofReal 4 * ∫⁻ z in Metric.ball (0 : V (nd X)) (min R0 ρ),
          ‖P (cpt X x z)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul_of_nonneg_left (lintegral_mono_set hmem) zero_le

theorem subMeanLoc_of (hLU : LUStatement (E := E)) : SubMeanLocStatement (E := E) := by
  intro r X la ρ hρ hρ1 x hx hxo
  obtain ⟨R0, hR0, hgood⟩ := good_ball X la
  have hR : 0 < min R0 ρ := lt_min hR0 hρ
  obtain ⟨Δ, zOf, bOf, hΔ, -, hz, hb, hdec, hinv⟩ := hLU r X x hxo
  have hx0 : (0 : V (nd X)) ∈ OmF X x := by
    show cpt X x 0 ∈ X.dom
    rw [cpt_zero]; exact hx
  obtain ⟨hΔx, hzx, hbx⟩ := hinv 0 hx0 (idF X) (idF_mem X)
  rw [rmul_idF, cpt_zero] at hΔx hzx hbx
  have hOo : IsOpen {y | y ∈ X.dom ∧ Δ y ≠ 0} :=
    (isOpenDom X).inter (isOpen_ne_fun hΔ.continuous continuous_const)
  have hxO : x ∈ {y | y ∈ X.dom ∧ Δ y ≠ 0} := ⟨hx, hΔx⟩
  have hzc : ContinuousAt zOf x := hz.continuousOn.continuousAt (hOo.mem_nhds hxO)
  have hbc : ContinuousAt (fun y => bchar la (bOf y)) x := by
    have h := bchar_contAt X la
    rw [← hbx] at h
    exact h.comp (hb.continuousOn.continuousAt (hOo.mem_nhds hxO))
  have e1 : ∀ᶠ y in 𝓝 x, y ∈ {y | y ∈ X.dom ∧ Δ y ≠ 0} := hOo.mem_nhds hxO
  have e2 : ∀ᶠ y in 𝓝 x, ‖zOf y‖ < min R0 ρ / 2 :=
    hzc.norm.eventually_lt continuousAt_const (by rw [hzx, norm_zero]; positivity)
  have e3 : ∀ᶠ y in 𝓝 x, ‖bchar la (bOf y)‖ < 2 :=
    hbc.norm.eventually_lt continuousAt_const (by rw [hbx, bchar_idF, norm_one]; norm_num)
  obtain ⟨ε, hε, hall⟩ := Metric.eventually_nhds_iff_ball.1 (e1.and (e2.and e3))
  set v := volume (Metric.ball (0 : V (nd X)) (min R0 ρ / 2)) with hv
  have hvpos : v ≠ 0 := (Metric.measure_ball_pos volume _ (by positivity)).ne'
  have hvtop : v ≠ ⊤ := measure_ball_lt_top.ne
  refine ⟨ε, hε, ENNReal.ofReal 4 * v⁻¹ * ENNReal.ofReal 4,
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hvpos))) ENNReal.ofReal_lt_top, fun P hP y hy => ?_⟩
  obtain ⟨⟨hyd, hΔy⟩, hzy, hby⟩ := hall y hy
  obtain ⟨hzO, hbB, hyeq⟩ := hdec y hyd hΔy
  have hPy : P y = bchar la (bOf y) * P (cpt X x (zOf y)) := by
    conv_lhs => rw [hyeq]
    exact hP.2 _ hzO _ hbB
  have hsub : Metric.ball (zOf y) (min R0 ρ / 2) ⊆ Metric.ball (0 : V (nd X)) (min R0 ρ) := by
    intro w hw
    rw [mem_ball_zero_iff]
    rw [Metric.mem_ball, dist_eq_norm] at hw
    calc ‖w‖ = ‖(w - zOf y) + zOf y‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - zOf y‖ + ‖zOf y‖ := norm_add_le _ _
      _ < min R0 ρ / 2 + min R0 ρ / 2 := add_lt_add hw hzy
      _ = min R0 ρ := by ring
  obtain ⟨hmemB, hint⟩ := ball_int_bound X la hgood hx hxo P
  have hu : DifferentiableOn ℂ (fun w => P (cpt X x w)) (Metric.ball (zOf y) (min R0 ρ / 2)) :=
    hP.1.comp (diff_cpt X x).differentiableOn fun w hw => (hmemB (hsub hw)).2
  have hmv := ReciprocityTheory.L2DbarEstimates.C.mv (nd X) (zOf y) (min R0 ρ / 2) (fun w => P (cpt X x w)) (fun _ => 1)
    hu measurable_const
  simp only [mul_one, one_mul, lintegral_const, Measure.restrict_apply_univ] at hmv
  rw [Measure.addHaar_ball_center] at hmv
  have hle : ‖P (cpt X x (zOf y))‖ₑ ^ 2 ≤
      v⁻¹ * ∫⁻ w in Metric.ball (zOf y) (min R0 ρ / 2), ‖P (cpt X x w)‖ₑ ^ 2 := by
    rw [← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl hvpos) (Or.inl hvtop)]
    exact hmv
  have hbb : ‖bchar la (bOf y)‖ₑ ^ 2 ≤ ENNReal.ofReal 4 := by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [norm_nonneg (bchar la (bOf y))])
  calc ‖P y‖ₑ ^ 2 = ‖bchar la (bOf y)‖ₑ ^ 2 * ‖P (cpt X x (zOf y))‖ₑ ^ 2 := by
        rw [hPy, enorm_mul, mul_pow]
    _ ≤ ENNReal.ofReal 4 * (v⁻¹ * (ENNReal.ofReal 4 * ∫⁻ w in Bset X x ρ,
          ‖P (cpt X x w)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w))))) := by
        refine mul_le_mul' hbb (hle.trans (mul_le_mul_of_nonneg_left ?_ zero_le))
        exact (lintegral_mono_set hsub).trans hint
    _ = _ := by ring

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
