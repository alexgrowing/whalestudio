import Formalism.HermitianCurvature.LevelRecursionCondNeeded
import Formalism.LatticeTheta.ThetaShiftInversion

namespace Formalism.FourierDecayAlt.P.PoissonSummationDecay

open Formalism.FourierDecayAlt.F7
open Finset Polynomial
open MeasureTheory Formalism.H
open scoped FourierTransform RealInnerProductSpace ENNReal

theorem poissonStep : PoissonStep := by
  intro V _ _ _ _ _ Λ _ _ φ x hPA hnn S
  obtain ⟨hs, hsum⟩ := hPA
  have hre := Complex.hasSum_re hsum
  have h1 := sum_le_hasSum S (fun l _ => by simpa using hnn l) hre
  simp only [Complex.ofReal_re] at h1
  refine h1.trans ?_
  rw [← Complex.ofReal_inv, Complex.re_ofReal_mul]
  unfold poissonBound
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (ZLattice.covolume_pos Λ volume).le)
  have hexp : ∀ μ : dual Λ, ‖Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ))‖ = 1 := by
    intro μ
    rw [Complex.norm_exp]
    simp
  set a : dual Λ → ℂ := fun μ => (𝓕 (fun v => (φ v : ℂ)) : V → ℂ) μ *
      Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ)) with ha
  have hsn := summable_norm_iff.mpr hs
  rw [← Summable.tsum_add_tsum_compl (s := ({0} : Set (dual Λ))) (hs.subtype _) (hs.subtype _), tsum_singleton,
    Complex.add_re]
  have h0 : a 0 = (𝓕 (fun v => (φ v : ℂ)) : V → ℂ) 0 := by
    simp [ha]
  rw [h0]
  gcongr
  refine (Complex.re_le_norm _).trans ((norm_tsum_le_tsum_norm (hsn.subtype _)).trans (le_of_eq ?_))
  refine tsum_congr fun μ => ?_
  simp only [ha]
  rw [norm_mul, hexp, mul_one]

section Summable

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ V]

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] [InnerProductSpace ℝ V] in
theorem loc_summable_pt (Λ : Submodule ℤ V) (φ : V → ℂ) (h : LocSummable Λ φ) (x : V) :
    Summable (fun l : Λ => φ ((l:V) + x)) := by
  obtain ⟨b, hb, hbd⟩ := h {x} isCompact_singleton
  exact Summable.of_norm_bounded hb (fun l => hbd l x rfl)

omit [MeasurableSpace V] [BorelSpace V] in
theorem loc_cont (Λ : Submodule ℤ V) (φ : V → ℂ) (hc : Continuous φ) (h : LocSummable Λ φ) :
    Continuous (fun x : V => ∑' l : Λ, φ ((l:V) + x)) := by
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  obtain ⟨b, hb, hbd⟩ := h (Metric.closedBall x₀ 1) (isCompact_closedBall x₀ 1)
  have hon : ContinuousOn (fun x : V => ∑' l : Λ, φ ((l : V) + x)) (Metric.closedBall x₀ 1) :=
    continuousOn_tsum (fun l => (hc.comp (continuous_const.add continuous_id)).continuousOn) hb
      (fun l x hx => hbd l x hx)
  exact hon.continuousAt (Metric.closedBall_mem_nhds x₀ one_pos)

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] [InnerProductSpace ℝ V] in
theorem loc_per (Λ : Submodule ℤ V) (φ : V → ℂ) (l₀ : Λ) (x : V) :
    ∑' l : Λ, φ ((l:V) + ((l₀:V) + x)) = ∑' l : Λ, φ ((l:V) + x) := by
  have := (Equiv.addRight l₀).tsum_eq (fun l : Λ => φ ((l : V) + x))
  rw [← this]
  refine tsum_congr fun l => ?_
  simp only [Equiv.coe_addRight, Submodule.coe_add, add_assoc]

theorem loc_integrable (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (φ : V → ℂ)
    (hc : Continuous φ) (h : LocSummable Λ φ) : Integrable φ := by
  let b := Module.Free.chooseBasis ℤ Λ
  have hD := ZLattice.isAddFundamentalDomain b (volume : Measure V)
  have hDb := ZSpan.fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ Λ)
  have hDm := ZSpan.fundamentalDomain_measurableSet (b.ofZLatticeBasis ℝ Λ)
  obtain ⟨c, hcs, hcb⟩ := h (closure (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ))) hDb.isCompact_closure
  haveI : VAddInvariantMeasure Λ V (volume : Measure V) := ⟨fun c s _ => measure_preimage_add volume (c : V) s⟩
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  rw [hD.lintegral_eq_tsum'']
  have hle : ∀ l : Λ, ∫⁻ x in ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ), ‖φ (l +ᵥ x)‖ₑ ≤
      ENNReal.ofReal |c l| * volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ)) := by
    intro l
    rw [← setLIntegral_const]
    refine setLIntegral_mono' hDm fun x hx => ?_
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal ((hcb l x (subset_closure hx)).trans (le_abs_self _))
  calc ∑' l : Λ, ∫⁻ x in ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ), ‖φ (l +ᵥ x)‖ₑ
      ≤ ∑' l : Λ, ENNReal.ofReal |c l| * volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ)) :=
        ENNReal.tsum_le_tsum hle
    _ = ENNReal.ofReal (∑' l, |c l|) * volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ)) := by
        rw [ENNReal.tsum_mul_right, ENNReal.ofReal_tsum_of_nonneg (fun _ => abs_nonneg _) hcs.abs]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hDb.measure_lt_top

theorem poissonSummable : PoissonSummable := by
  intro V _ _ _ _ _ Λ _ _ φ hc hloc hsum x
  have hint := loc_integrable Λ φ hc hloc
  let b := Module.Free.chooseBasis ℤ Λ
  have hD := ZLattice.isAddFundamentalDomain b (volume : Measure V)
  have hGc : Continuous (fun y : V => ∑' l : Λ, φ ((l : V) + y)) := loc_cont Λ φ hc hloc
  have hGp : ∀ (l : Λ) (y : V), (fun y : V => ∑' l : Λ, φ ((l : V) + y)) ((l : V) + y) =
      (fun y : V => ∑' l : Λ, φ ((l : V) + y)) y := fun l y => loc_per Λ φ l y
  have hcoef : ∀ μ : dual Λ, ∫ y in ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ),
      (fun y : V => ∑' l : Λ, φ ((l : V) + y)) y *
        Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : V), y⟫ : ℝ))) = (𝓕 φ : V → ℂ) μ :=
    fun μ => unfoldCoeff_main Λ φ hint _ hD μ μ.2
  have hsumF : Summable (fun μ : dual Λ => (𝓕 φ : V → ℂ) μ) := summable_norm_iff.mp hsum
  have hLFS := lattice_fourier_series V Λ _ hGc hGp _ hD (by simpa only [hcoef] using hsumF) x
  simp only [hcoef] at hLFS
  have hexp : ∀ μ : dual Λ, ‖Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ))‖ = 1 := by
    intro μ
    rw [Complex.norm_exp]
    simp
  refine ⟨Summable.of_norm_bounded hsum (fun μ => by rw [norm_mul, hexp, mul_one]), ?_⟩
  have hG : (∑' l : Λ, φ ((l : V) + x)) = (ZLattice.covolume Λ : ℂ)⁻¹ * ∑' μ : dual Λ,
      (𝓕 φ : V → ℂ) μ * Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ)) := by
    rw [← hLFS.tsum_eq, ← tsum_mul_left]
    exact tsum_congr fun μ => mul_assoc _ _ _
  rw [← hG]
  exact (loc_summable_pt Λ φ hloc x).hasSum

end Summable

section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type} [Fintype ι]

noncomputable def gP (π : ι → V →L[ℝ] ℂ) (c : V) : ℝ := ∏ v, ((1 + ‖π v c‖) ^ 3)⁻¹

theorem gP_pos (π : ι → V →L[ℝ] ℂ) (c : V) : 0 < gP π c :=
  Finset.prod_pos fun v _ => by positivity

theorem gP_mul_le_gP_add (π : ι → V →L[ℝ] ℂ) (c u : V) : gP π c * gP π u ≤ gP π (c + u) := by
  unfold gP
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun v _ => by positivity) (fun v _ => ?_)
  rw [← mul_inv, ← mul_pow]
  apply inv_anti₀ (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  have := norm_add_le (π v c) (π v u)
  rw [map_add]
  nlinarith [norm_nonneg (π v c), norm_nonneg (π v u), mul_nonneg (norm_nonneg (π v c)) (norm_nonneg (π v u))]

theorem le_gP_of_norm_le (π : ι → V →L[ℝ] ℂ) (R : ℝ) (x : V) (hx : ‖x‖ ≤ R) :
    ∏ v, ((1 + ‖π v‖ * R)^3)⁻¹ ≤ gP π x := by
  have hR0 : 0 ≤ R := (norm_nonneg x).trans hx
  unfold gP
  refine Finset.prod_le_prod (fun v _ => inv_nonneg.mpr (pow_nonneg (by positivity) 3)) (fun v _ => ?_)
  apply inv_anti₀ (pow_pos (by positivity) 3)
  apply pow_le_pow_left₀ (by positivity)
  have h1 := (π v).le_opNorm x
  have h2 : ‖π v‖ * ‖x‖ ≤ ‖π v‖ * R := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
  linarith

theorem gP_integrable [MeasurableSpace V] [BorelSpace V] (π : ι → V →L[ℝ] ℂ)
    (hπ : Function.Bijective fun (c : V) (v : ι) => π v c) : Integrable (gP π) := by
  let L : V →ₗ[ℝ] (ι → ℂ) := LinearMap.pi fun v => (π v).toLinearMap
  let T : V ≃L[ℝ] (ι → ℂ) := (LinearEquiv.ofBijective L hπ).toContinuousLinearEquiv
  have h1 : Integrable (fun w : ℂ => ((1 + ‖w‖) ^ 3)⁻¹) := by
    have := integrable_one_add_norm (E := ℂ) (μ := volume) (r := 3) (by simp; norm_num)
    refine this.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only
    rw [Real.rpow_neg (by positivity)]
    norm_cast
  have hg : Integrable (fun z : ι → ℂ => ∏ v, ((1 + ‖z v‖) ^ 3)⁻¹) :=
    Integrable.fintype_prod (f := fun _ w => ((1 + ‖w‖) ^ 3)⁻¹) (μ := fun _ => volume) fun _ => h1
  haveI : (Measure.map T (volume : Measure V)).IsAddHaarMeasure := T.isAddHaarMeasure_map _
  have hmap := Measure.isAddLeftInvariant_eq_smul (Measure.map T (volume : Measure V)) (volume : Measure (ι → ℂ))
  have hg' : Integrable (fun z : ι → ℂ => ∏ v, ((1 + ‖z v‖) ^ 3)⁻¹) (Measure.map T (volume : Measure V)) := by
    rw [hmap]
    exact hg.smul_measure_nnreal
  have := (integrable_map_equiv T.toHomeomorph.toMeasurableEquiv _).mp hg'
  exact this

theorem gP_summable [MeasurableSpace V] [BorelSpace V] (π : ι → V →L[ℝ] ℂ)
    (hπ : Function.Bijective fun (c : V) (v : ι) => π v c)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    Summable (fun l : Λ => gP π l) := by
  let b := Module.Free.chooseBasis ℤ Λ
  have hD := ZLattice.isAddFundamentalDomain b (volume : Measure V)
  have hDb := ZSpan.fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ Λ)
  have hDm := ZSpan.fundamentalDomain_measurableSet (b.ofZLatticeBasis ℝ Λ)
  obtain ⟨R, hR0, hR⟩ := hDb.subset_closedBall_lt 0 0
  have hm : 0 < ∏ v, ((1 + ‖π v‖ * R) ^ 3)⁻¹ :=
    Finset.prod_pos fun v _ => inv_pos.mpr (pow_pos (by positivity) 3)
  have hvol : volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ)) ≠ 0 := by
    intro h0
    have h1 := ZLattice.covolume_eq_measure_fundamentalDomain Λ volume hD
    have h2 := ZLattice.covolume_pos Λ volume
    rw [h1, Measure.real, h0, ENNReal.toReal_zero] at h2
    exact lt_irrefl _ h2
  haveI : VAddInvariantMeasure Λ V (volume : Measure V) := ⟨fun c s _ => measure_preimage_add volume (c : V) s⟩
  have hint := (gP_integrable π hπ).lintegral_lt_top
  rw [hD.lintegral_eq_tsum''] at hint
  have hge : ∀ l : Λ, ENNReal.ofReal (gP π l) *
      (ENNReal.ofReal (∏ v, ((1 + ‖π v‖ * R) ^ 3)⁻¹) * volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ))) ≤
      ∫⁻ x in ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ), ENNReal.ofReal (gP π (l +ᵥ x)) := by
    intro l
    rw [← mul_assoc, ← ENNReal.ofReal_mul (gP_pos π l).le, ← setLIntegral_const]
    refine setLIntegral_mono' hDm fun x hx => ENNReal.ofReal_le_ofReal ?_
    have hx' : ‖x‖ ≤ R := by simpa using hR hx
    exact (mul_le_mul_of_nonneg_left (le_gP_of_norm_le π R x hx') (gP_pos π l).le).trans (gP_mul_le_gP_add π l x)
  have htop : ∑' l : Λ, ENNReal.ofReal (gP π l) ≠ ⊤ := by
    intro htop
    have hle := ENNReal.tsum_le_tsum hge
    rw [ENNReal.tsum_mul_right, htop, ENNReal.top_mul (mul_ne_zero (ENNReal.ofReal_pos.mpr hm).ne' hvol)] at hle
    exact absurd (lt_of_le_of_lt hle hint) (lt_irrefl _)
  have := ENNReal.summable_toReal htop
  refine this.congr fun l => ?_
  exact ENNReal.toReal_ofReal (gP_pos π l).le
end

private theorem nonneg_of_norm_le_mul_gP {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {ι : Type} [Fintype ι] (π : ι → V →L[ℝ] ℂ) (φ : V → ℂ) (C : ℝ)
    (hφ' : ∀ c, ‖φ c‖ ≤ C * gP π c) : 0 ≤ C := by
  by_contra hneg
  have hneg' : C < 0 := lt_of_not_ge hneg
  have h1 : C * gP π 0 < 0 := mul_neg_of_neg_of_pos hneg' (gP_pos π 0)
  have h2 : ‖φ 0‖ ≤ C * gP π 0 := hφ' 0
  have h3 : 0 ≤ ‖φ 0‖ := norm_nonneg _
  linarith

private theorem gP_add_mul_prod_inv_le_gP_of_norm_le {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {ι : Type} [Fintype ι] (π : ι → V →L[ℝ] ℂ) (R : ℝ) (y x : V)
    (hx : ‖-x‖ ≤ R) : gP π (y + x) * ∏ v, ((1 + ‖π v‖ * R) ^ 3)⁻¹ ≤ gP π y := by
  calc gP π (y + x) * ∏ v, ((1 + ‖π v‖ * R) ^ 3)⁻¹
      ≤ gP π (y + x) * gP π (-x) :=
        mul_le_mul_of_nonneg_left (le_gP_of_norm_le π R (-x) hx) (gP_pos _ _).le
    _ ≤ gP π (y + x + -x) := gP_mul_le_gP_add π _ _
    _ = gP π y := by rw [add_neg_cancel_right]

private theorem norm_add_le_mul_gP_div_prod_of_norm_le {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {ι : Type} [Fintype ι] (π : ι → V →L[ℝ] ℂ) (φ : V → ℂ) (C R : ℝ)
    (hC : 0 ≤ C) (hR0 : 0 < R) (hφ' : ∀ c, ‖φ c‖ ≤ C * gP π c) (y x : V) (hx : ‖x‖ ≤ R) :
    ‖φ (y + x)‖ ≤ C * gP π y / ∏ v, ((1 + ‖π v‖ * R) ^ 3)⁻¹ := by
  have hm : 0 < ∏ v, ((1 + ‖π v‖ * R) ^ 3)⁻¹ := by
    refine Finset.prod_pos fun v _ => inv_pos.mpr (pow_pos ?_ 3)
    have := mul_nonneg (norm_nonneg (π v)) hR0.le
    linarith
  have hx' : ‖-x‖ ≤ R := by rw [norm_neg]; exact hx
  have h1 := gP_add_mul_prod_inv_le_gP_of_norm_le π R y x hx'
  have h3 : gP π (y + x) ≤ gP π y / ∏ v, ((1 + ‖π v‖ * R) ^ 3)⁻¹ := (le_div_iff₀ hm).mpr h1
  calc ‖φ (y + x)‖ ≤ C * gP π (y + x) := hφ' _
    _ ≤ C * (gP π y / ∏ v, ((1 + ‖π v‖ * R) ^ 3)⁻¹) := mul_le_mul_of_nonneg_left h3 hC
    _ = C * gP π y / ∏ v, ((1 + ‖π v‖ * R) ^ 3)⁻¹ := (mul_div_assoc _ _ _).symm

private theorem locSummable_of_norm_le_mul_gP {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {ι : Type} [Fintype ι]
    (π : ι → V →L[ℝ] ℂ) (hπ : Function.Bijective fun (c : V) (v : ι) => π v c)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (φ : V → ℂ) (C : ℝ)
    (hφ' : ∀ c, ‖φ c‖ ≤ C * gP π c) : LocSummable Λ φ := by
  have hC : 0 ≤ C := nonneg_of_norm_le_mul_gP π φ C hφ'
  intro Kc hK
  obtain ⟨R, hR0, hR⟩ := hK.isBounded.subset_closedBall_lt 0 0
  have hs : Summable (fun l : Λ => C * gP π (l : V) / ∏ v, ((1 + ‖π v‖ * R) ^ 3)⁻¹) :=
    ((gP_summable π hπ Λ).mul_left C).div_const _
  refine ⟨_, hs, fun l x hx => ?_⟩
  have hxR : ‖x‖ ≤ R := by
    have := hR hx
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  exact norm_add_le_mul_gP_div_prod_of_norm_le π φ C R hC hR0 hφ' (l : V) x hxR

theorem productDecay : ProductDecaySummable := by
  intro V _ _ _ ι _ π hπ Λ _ _ φ C hφ
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  exact locSummable_of_norm_le_mul_gP π hπ Λ φ C hφ

theorem stepDecay (h : PoissonStep) : PoissonStepDecay := by
  intro V _ _ _ _ _ hP Λ _ _ φ b x hc hb h1 h2 hnn S
  exact h V Λ φ x (hP Λ (fun v => (φ v : ℂ)) (Complex.continuous_ofReal.comp hc) b hb h1 h2 x) hnn S

theorem stepText (h : PoissonStep) (h2 : PoissonSummable) (h3 : ProductDecaySummable) :
    PoissonStepText := by
  intro V _ _ _ _ _ ι _ π hπ Λ _ _ φ C x hc hφ hsum hnn
  have hloc : LocSummable Λ (fun v => (φ v : ℂ)) :=
    h3 V ι π hπ Λ (fun v => (φ v : ℂ)) C (fun c => by simpa [Complex.norm_real] using hφ c)
  have hPA := h2 V Λ (fun v => (φ v : ℂ)) (Complex.continuous_ofReal.comp hc) hloc hsum x
  exact ⟨hPA, h V Λ φ x hPA hnn⟩

end Formalism.FourierDecayAlt.P.PoissonSummationDecay

namespace Formalism.FourierDecayAlt.P

theorem poisson_summation_level : Formalism.FourierDecayAlt.F7.PoissonStep := PoissonSummationDecay.poissonStep

theorem poisson_level_decay : Formalism.FourierDecayAlt.F7.PoissonStepDecay :=
  PoissonSummationDecay.stepDecay PoissonSummationDecay.poissonStep

theorem poisson_series_summable : Formalism.FourierDecayAlt.F7.PoissonSummable := PoissonSummationDecay.poissonSummable

theorem product_decay_summable : Formalism.FourierDecayAlt.F7.ProductDecaySummable := PoissonSummationDecay.productDecay

theorem poisson_summation_level_statement : Formalism.FourierDecayAlt.F7.PoissonStepText :=
  PoissonSummationDecay.stepText PoissonSummationDecay.poissonStep PoissonSummationDecay.poissonSummable PoissonSummationDecay.productDecay

end Formalism.FourierDecayAlt.P
