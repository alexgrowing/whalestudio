import Development.WeilBound.CoreStatements.OrbitDecayEstimates.CurveDerivativeDecay.HIntegrability

noncomputable section

open Matrix Finset MeasureTheory Formalism.REAL Formalism.MainNotions.S Filter Topology GlobalTheory.CompanionTheory.PairingAnalysis
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.Lime.T3

open ReciprocityTheory.ChartRestriction.DS (smD smE actM)

theorem volume_ratio_bound : VolR := fun _ ε μ _ hm _ _ hδ hδ2 hR => vol_ratio hm ε μ hδ hδ2 hR

theorem decay_estimate : Decay := by
  intro m N ε lam A _ _ _ π hm hmN hl hDS hg v hv hv1 g₀ Y hY g
  have hN : 1 ≤ 12 * N ^ 2 := by have : 1 ≤ N := hm.trans hmN; nlinarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 := dec_conj hm hDS.2.2.1 (by positivity) (dec_low hm hmN hl hDS hg hv hv1 hN le_rfl) g₀ g
  have h2 := one_le_nG hm g
  have h3 : 0 ≤ hs (uMat g₀) := by rw [← nG_sq]; positivity
  have e1 : (Real.exp 1 * Real.sqrt m) ^ (12 * N ^ 2) =
      Real.exp (6 * (N : ℝ) ^ 2 * Real.log m + 12 * (N : ℝ) ^ 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hm0, ← Real.exp_add, ← Real.exp_nat_mul]
    congr 1
    push_cast; ring
  have e2 : (nG g)⁻¹ ^ (12 * N ^ 2) = hs (um g) ^ (-(6 * (N : ℝ) ^ 2)) := by
    change _ = hs (uMat g) ^ _
    rw [← nG_sq, ← Real.rpow_natCast (nG g) 2, ← Real.rpow_mul (by linarith), inv_pow, ← Real.rpow_natCast,
      ← Real.rpow_neg (by linarith)]
    congr 1
    push_cast; ring
  rw [e1, e2] at h1
  refine h1.trans ?_
  have h4 : 0 ≤ hs (um g) ^ (-(6 * (N : ℝ) ^ 2)) := by rw [← e2]; positivity
  gcongr

theorem integral_ratio_bound : IntR := by
  intro m ε μ hμ hm φ C a hφ ha hd
  have hC : 0 ≤ C := by
    have h1 := (norm_nonneg _).trans (hd 1)
    have h2 : 0 < hs (um (1 : UJ ε)) ^ (-a) := Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (one_le_hsG hm 1)) _
    exact nonneg_of_mul_nonneg_left h1 h2
  have hd' : ∀ g, ‖φ g‖ ≤ C * (nG g)⁻¹ ^ (2 * m ^ 2 + 1) := fun g =>
    (hd g).trans (mul_le_mul_of_nonneg_left (rpow_hs hm g _ (by push_cast; linarith)) hC)
  have hI := integrable_of_dec hm μ hφ hC le_rfl hd'
  refine ⟨hI, ?_⟩
  have h1 := lint_le hm μ hC one_pos le_rfl hd'
  rw [integral_norm_eq_lintegral_enorm hI.1]
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (nearSet_lt_top ε μ).ne) h1).trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), div_one]
  rfl

theorem derivative_upper_bound : DUp := by
  intro m ε lam B A _ _ _ π μ d hμ hm hl hDS hB hg hd
  have hπ : IsURepOn (UJset ε) π := hDS.2.2.1
  obtain ⟨S, hS⟩ := hDS.2.2.2.2.2.1
  obtain ⟨v0, hv0, hne, -⟩ := hS.2.2.2.1
  have hn0 : 0 < ‖v0‖ := norm_pos_iff.2 hne
  set v : A := ((‖v0‖⁻¹ : ℝ) : ℂ) • v0 with hvd
  have hv : v ∈ lowKSub ε lam π := Submodule.smul_mem _ _ (le_sSup (s := {S | IsKTypeOf ε π (Formalism.QuantumDeterminants.lowK ε lam) S}) hS hv0)
  have hv1 : ‖v‖ = 1 := by
    rw [hvd, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ hn0.ne']
  obtain ⟨x, hx, hb, -⟩ := low_bounds hm hl hDS hB hg hv hv1
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hB0 : 0 ≤ B := by have := le_four_mul hm hl hB; linarith
  set K : ℝ := 100 * m * (B + 1) with hK
  have hK1 : 200 ≤ K := by nlinarith
  have hsq : Real.sqrt m ≤ m := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hnear : ∀ g ∈ nearSet ε (K ^ 2)⁻¹, 1 / 4 ≤ ‖⟪v, π (uMat g) v⟫_ℂ‖ ^ 2 := by
    intro g hgn
    have hδ : (K ^ 2)⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith
    have h1 := disp_le hπ x hb (by positivity) hδ hgn
    rw [hx] at h1
    have h2 : 7 * (K ^ 2)⁻¹ * (8 * Real.sqrt m * (B + 2)) ≤ 1 / 2 := by
      have a1 : 8 * Real.sqrt m * (B + 2) ≤ K := by
        have : Real.sqrt m * (B + 2) ≤ m * (2 * (B + 1)) := mul_le_mul hsq (by linarith) (by linarith) (by linarith)
        nlinarith
      rw [mul_assoc, ← div_eq_inv_mul, ← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith
    have h3 : ‖⟪v, π (uMat g) v - v⟫_ℂ‖ ≤ 1 / 2 := by
      refine (norm_inner_le_norm _ _).trans ?_
      rw [hv1, one_mul]
      exact h1.trans h2
    rw [inner_sub_right, inner_self_eq_norm_sq_to_K, hv1] at h3
    have h4 := norm_sub_norm_le (1 : ℂ) (1 - ⟪v, π (uMat g) v⟫_ℂ)
    rw [sub_sub_cancel, norm_one, norm_sub_rev] at h4
    have h5 : ‖⟪v, π (uMat g) v⟫_ℂ - 1‖ ≤ 1 / 2 := by simpa using h3
    nlinarith [norm_nonneg ⟪v, π (uMat g) v⟫_ℂ]
  obtain ⟨hI, hE⟩ := hd.2 v v v v
  have e1 : ∀ g : UJ ε, coefOn π v v g * star (coefOn π v v g) = ((‖⟪v, π (uMat g) v⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rfl
  simp only [e1] at hI hE
  have hI' : Integrable (fun g : UJ ε => ‖⟪v, π (uMat g) v⟫_ℂ‖ ^ 2) μ :=
    hI.re.congr (Filter.Eventually.of_forall fun g => Complex.ofReal_re _)
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K, hv1] at hE
  have hE' : ∫ g : UJ ε, ‖⟪v, π (uMat g) v⟫_ℂ‖ ^ 2 ∂μ = d⁻¹ := by
    have : ((∫ g : UJ ε, ‖⟪v, π (uMat g) v⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) = ((d⁻¹ : ℝ) : ℂ) := by rw [hE]; simp
    exact_mod_cast this
  have hmeas : MeasurableSet (nearSet ε (K ^ 2)⁻¹) :=
    (isClosed_le (continuous_hs_real_place_taylor.comp ((continuous_coeMatrix ε).sub continuous_const)) continuous_const).measurableSet
  have h6 : ENNReal.ofReal (1 / 4) * μ (nearSet ε (K ^ 2)⁻¹) ≤ ENNReal.ofReal d⁻¹ := by
    rw [← hE', ofReal_integral_eq_lintegral_ofReal hI' (Filter.Eventually.of_forall fun g => by positivity),
      ← lintegral_indicator_const hmeas]
    refine lintegral_mono fun g => ?_
    by_cases hg' : g ∈ nearSet ε (K ^ 2)⁻¹
    · rw [Set.indicator_of_mem hg']; exact ENNReal.ofReal_le_ofReal (hnear g hg')
    · rw [Set.indicator_of_notMem hg']; exact bot_le
  have hd0 := hd.1
  calc ENNReal.ofReal d * μ (nearSet ε (K ^ 2)⁻¹)
      = ENNReal.ofReal (4 * d) * (ENNReal.ofReal (1 / 4) * μ (nearSet ε (K ^ 2)⁻¹)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]; congr 2; ring
    _ ≤ ENNReal.ofReal (4 * d) * ENNReal.ofReal d⁻¹ := mul_le_mul_right h6 _
    _ = 4 := by
        rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, mul_inv_cancel₀ hd0.ne', mul_one]; simp

end CompanionTheory.Lime.T3
