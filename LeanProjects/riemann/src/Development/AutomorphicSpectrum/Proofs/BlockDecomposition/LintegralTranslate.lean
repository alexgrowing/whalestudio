import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E.E3 PositivityTheory.Rg.BcB

namespace GlobalTheory.CompanionTheory.CentRe

theorem no_growth (b I K : ℝ) (M : ℕ) (hb : 0 < b) (hI : 0 < I)
    (h : ∀ s : ℝ, 0 ≤ s → I * Real.exp (b * s) ≤ K * (1 + s) ^ M) : False := by
  set K' : ℝ := K / b ^ M / I * Real.exp b with hK'
  obtain ⟨x, hx1, hx2⟩ := (((Real.tendsto_exp_div_pow_atTop M).eventually_gt_atTop K').and
    (eventually_ge_atTop b)).exists
  have hx0 : 0 < x := lt_of_lt_of_le hb hx2
  have hs : 0 ≤ x / b - 1 := by
    rw [sub_nonneg, le_div_iff₀ hb]; linarith
  have hh := h _ hs
  rw [lt_div_iff₀ (pow_pos hx0 M)] at hx1
  have h1 : I * Real.exp (-b) * (K' * x ^ M) < I * Real.exp (-b) * Real.exp x :=
    mul_lt_mul_of_pos_left hx1 (mul_pos hI (Real.exp_pos _))
  have e1 : I * Real.exp (-b) * (K' * x ^ M) = K * (1 + (x / b - 1)) ^ M := by
    have hE := Real.exp_pos b
    rw [hK', Real.exp_neg, show 1 + (x / b - 1) = x / b by ring, div_pow]
    field_simp
  have e2 : I * Real.exp (-b) * Real.exp x = I * Real.exp (b * (x / b - 1)) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring
  rw [e1, e2] at h1
  exact absurd hh (not_le.2 h1)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem lintegral_translate [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure]
    (φ : GA E N → ℂ) (z : ℂ) (hz : ∀ (t : ℝ) g, φ (splitCentre E N t * g) = Complex.exp (z * t) * φ g)
    (t : ℝ) (Q : Set (GA E N)) :
    ∫⁻ g in (fun q => splitCentre E N t * q) '' Q, ‖φ g‖ₑ ^ 2 ∂μ =
      ENNReal.ofReal (Real.exp (2 * z.re * t)) * ∫⁻ g in Q, ‖φ g‖ₑ ^ 2 ∂μ := by
  rw [← (measurePreserving_mul_left μ (splitCentre E N t)).setLIntegral_comp_emb
    (measurableEmbedding_mulLeft _) (fun g => ‖φ g‖ₑ ^ 2) Q,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun g => ?_
  rw [hz, enorm_mul, mul_pow]
  congr 1
  rw [← ofReal_norm_eq_enorm, Complex.norm_exp, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
  congr 2
  simp
  ring

theorem centReGlue_holds : CentReGlue := by
  intro hS hM E _ _ _ N φ z hφ hne hL hz
  letI : MeasurableSpace (GA E N) := borel _
  haveI : BorelSpace (GA E N) := ⟨rfl⟩
  obtain ⟨C, M, hC⟩ := hL Measure.haar inferInstance
  by_contra ha
  obtain ⟨x₀, hx₀⟩ : ∃ x, φ x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (funext hcon)
  obtain ⟨Q, hQ, hQn⟩ := exists_compact_mem_nhds x₀
  obtain ⟨n, hn⟩ := hM E N Q hQ
  obtain ⟨C₁, hC₁, hsz⟩ := hS E N {1} Q isCompact_singleton hQ
  set I : ENNReal := ∫⁻ g in Q, ‖φ g‖ₑ ^ 2 ∂(Measure.haar : Measure (GA E N)) with hI
  have key : ∀ t : ℝ, ENNReal.ofReal (Real.exp (2 * z.re * t)) * I ≤
      ENNReal.ofReal (C * n * (1 + C₁ * (1 + |t|)) ^ M) := by
    intro t
    rw [hI, ← lintegral_translate _ φ z hz t Q]
    refine hC _ (hQ.image (continuous_const.mul continuous_id)) n _ (by positivity) (hn _ ?_) ?_
    · exact fun g => GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm t g
    · rintro _ ⟨q, hq, rfl⟩
      have h1 := hsz 1 rfl q hq (fun _ => t)
      rw [one_mul, PositivityTheory.Rg.Rs.JDict.tor_const] at h1
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ hC₁)
      have : ‖(fun _ : Fin N => t)‖ ≤ |t| :=
        (pi_norm_le_iff_of_nonneg (abs_nonneg t)).2 fun _ => (Real.norm_eq_abs t).le
      linarith
  have hIpos : 0 < I := by
    rw [hI, setLIntegral_pos_iff (hφ.measurable.enorm.pow_const 2)]
    have hV : IsOpen (interior Q ∩ {x | φ x ≠ 0}) :=
      isOpen_interior.inter (isOpen_ne_fun hφ continuous_const)
    have hVne : (interior Q ∩ {x | φ x ≠ 0}).Nonempty :=
      ⟨x₀, mem_interior_iff_mem_nhds.2 hQn, hx₀⟩
    refine (hV.measure_pos _ hVne).trans_le (measure_mono ?_)
    rintro x ⟨hx1, hx2⟩
    refine ⟨?_, interior_subset hx1⟩
    simpa [Function.mem_support] using hx2
  have hItop : I ≠ ⊤ := by
    have h0 := key 0
    simp only [mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul] at h0
    exact (h0.trans_lt ENNReal.ofReal_lt_top).ne
  have hI' : 0 < I.toReal := ENNReal.toReal_pos hIpos.ne' hItop
  have key' : ∀ t : ℝ, I.toReal * Real.exp (2 * z.re * t) ≤ C * n * (1 + C₁ * (1 + |t|)) ^ M := by
    intro t
    have h := key t
    rw [← ENNReal.ofReal_toReal hItop, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ENNReal.ofReal_le_ofReal_iff'] at h
    rcases h with h | h
    · rwa [mul_comm]
    · exact absurd h (not_le.2 (mul_pos (Real.exp_pos _) hI'))
  refine no_growth (2 * |z.re|) I.toReal (|C * n| * (1 + C₁) ^ M) M
    (by have := abs_pos.2 ha; positivity) hI' fun s hs => ?_
  have hsign : ∃ t : ℝ, 2 * z.re * t = 2 * |z.re| * s ∧ |t| = s := by
    rcases le_total 0 z.re with h | h
    · exact ⟨s, by rw [abs_of_nonneg h], abs_of_nonneg hs⟩
    · exact ⟨-s, by rw [abs_of_nonpos h]; ring, by rw [abs_neg, abs_of_nonneg hs]⟩
  obtain ⟨t, ht1, ht2⟩ := hsign
  have h := key' t
  rw [ht1, ht2] at h
  refine h.trans ?_
  have hb : 1 + C₁ * (1 + s) ≤ (1 + C₁) * (1 + s) := by nlinarith
  calc C * n * (1 + C₁ * (1 + s)) ^ M ≤ |C * n| * (1 + C₁ * (1 + s)) ^ M :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ |C * n| * ((1 + C₁) * (1 + s)) ^ M :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb M) (abs_nonneg _)
    _ = |C * n| * (1 + C₁) ^ M * (1 + s) ^ M := by rw [mul_pow, mul_assoc]

end GlobalTheory.CompanionTheory.CentRe

end
