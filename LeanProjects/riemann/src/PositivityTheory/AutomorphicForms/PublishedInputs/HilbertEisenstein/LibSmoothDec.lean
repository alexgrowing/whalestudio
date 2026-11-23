import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.ContDiffOnOfContDiffAtOne

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap ContDiff Topology
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

section General

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

theorem integrable_fderiv_schwartz_bilin (Ψ : 𝓢(V, ℂ)) (B : V →L[ℝ] X →L[ℝ] V) {U : Set X} {c : ℝ}
    (hc : 0 < c) (hB : ∀ x ∈ U, ∀ v, c * ‖v‖ ≤ ‖B v x‖)
    {κ : α → ℂ} {w : α → V} (hκ : AEStronglyMeasurable κ μ) (hw : AEStronglyMeasurable w μ)
    {k : ℕ} (hint : Integrable (fun a => ‖κ a‖ * ((1 + ‖w a‖) ^ k)⁻¹) μ) {x : X} (hx : x ∈ U) :
    Integrable (fun a => κ a • fderiv ℝ (fun x => Ψ (B (w a) x)) x) μ := by
  obtain ⟨C, -, hC⟩ := exists_bound_bilD Ψ B hc hB 1 k
  refine (hint.const_mul C).mono' (hκ.smul ((continuous_fderiv_bil_left Ψ B x).comp_aestronglyMeasurable hw))
    (ae_of_all _ fun a => ?_)
  have h := hC x hx (w a)
  rw [bilD, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero] at h
  rw [norm_smul]
  calc ‖κ a‖ * ‖fderiv ℝ (fun x => Ψ (B (w a) x)) x‖ ≤ ‖κ a‖ * (C * ((1 + ‖w a‖) ^ k)⁻¹) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = C * (‖κ a‖ * ((1 + ‖w a‖) ^ k)⁻¹) := by ring

end General

theorem fderiv_mul_comp_integral {P : Type*} [MeasurableSpace P] {μ : Measure P}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : P → E → ℂ} {h' : P → E →L[ℝ] ℂ} {z0 : E}
    (hh : ∀ᵐ p ∂μ, HasFDerivAt (h p) (h' p) z0) (hi1 : Integrable h' μ)
    (hi0 : Integrable (fun p => h p z0) μ)
    {H : E → ℂ} (HI : HasFDerivAt H (∫ p, h' p ∂μ) z0) (hH0 : H z0 = ∫ p, h p z0 ∂μ)
    {a : E → ℂ} {a' : E →L[ℝ] ℂ} {b : E → E} {b' : E →L[ℝ] E} {x0 : E}
    (ha : HasFDerivAt a a' x0) (hb : HasFDerivAt b b' x0) (hb0 : b x0 = z0) (X : E) :
    Integrable (fun p => fderiv ℝ (fun x => a x * h p (b x)) x0 X) μ ∧
      DifferentiableAt ℝ (fun x => a x * H (b x)) x0 ∧
      fderiv ℝ (fun x => a x * H (b x)) x0 X = ∫ p, fderiv ℝ (fun x => a x * h p (b x)) x0 X ∂μ := by
  have hae : ∀ᵐ p ∂μ, fderiv ℝ (fun x => a x * h p (b x)) x0 X =
      a x0 * h' p (b' X) + h p z0 * a' X := by
    filter_upwards [hh] with p hp
    have hp' : HasFDerivAt (h p) (h' p) (b x0) := by rw [hb0]; exact hp
    have hc : HasFDerivAt (fun x => a x * h p (b x)) _ x0 := ha.mul (hp'.comp x0 hb)
    rw [hc.fderiv]
    simp [hb0]
  have HI' : HasFDerivAt H (∫ p, h' p ∂μ) (b x0) := by rw [hb0]; exact HI
  have hbig : HasFDerivAt (fun x => a x * H (b x)) _ x0 := ha.mul (HI'.comp x0 hb)
  have hint : Integrable (fun p => a x0 * h' p (b' X) + h p z0 * a' X) μ :=
    ((hi1.apply_continuousLinearMap (b' X)).const_mul _).add (hi0.mul_const _)
  refine ⟨hint.congr (hae.mono fun p hp => hp.symm), hbig.differentiableAt, ?_⟩
  rw [hbig.fderiv, integral_congr_ae hae, integral_add ((hi1.apply_continuousLinearMap (b' X)).const_mul _)
    (hi0.mul_const _), integral_const_mul, integral_mul_const, ← hH0,
    ← ContinuousLinearMap.integral_apply hi1 (b' X)]
  simp [hb0]

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem eventually_good (_g : GA F 2) : ∀ᶠ x in 𝓝 (UpperTheory.V.TR.oneL F 2),
    x ∈ Metric.ball (UpperTheory.V.TR.oneL F 2) (1 / 4) ∧ invL x ∈ Metric.ball (UpperTheory.V.TR.oneL F 2) (1 / 4) ∧
      x ∈ UpperTheory.V.TR.invSet F 2 ∧ ∀ v, 0 < (Matrix.of x).det v := by
  have hU : IsOpen (Metric.ball (UpperTheory.V.TR.oneL F 2) (1 / 4 : ℝ)) := Metric.isOpen_ball
  have h1U : UpperTheory.V.TR.oneL F 2 ∈ Metric.ball (UpperTheory.V.TR.oneL F 2) (1 / 4 : ℝ) :=
    Metric.mem_ball_self (by norm_num)
  have hinv : ∀ᶠ x in 𝓝 (UpperTheory.V.TR.oneL F 2), invL x ∈ Metric.ball (UpperTheory.V.TR.oneL F 2) (1 / 4 : ℝ) :=
    contDiffAt_invL.continuousAt.preimage_mem_nhds (by rw [invL_one]; exact hU.mem_nhds h1U)
  have hunit : ∀ᶠ x in 𝓝 (UpperTheory.V.TR.oneL F 2), x ∈ UpperTheory.V.TR.invSet F 2 :=
    UpperTheory.V.TR.isOpen_invSet.mem_nhds (by simp [UpperTheory.V.TR.invSet, UpperTheory.V.TR.oneL, UpperTheory.V.TR.toL])
  have hdet : ∀ᶠ x in 𝓝 (UpperTheory.V.TR.oneL F 2), ∀ v, 0 < (Matrix.det (Matrix.of x)) v := by
    refine Filter.eventually_all.2 fun v => ?_
    have hcont : ContinuousAt (fun x : UpperTheory.V.TR.Lie F 2 => (Matrix.det (Matrix.of x)) v) (UpperTheory.V.TR.oneL F 2) :=
      ((continuous_apply v).comp (UpperTheory.V.TR.contDiff_det (E := F) (a := 2)).continuous).continuousAt
    exact continuousAt_const.eventually_lt hcont (by simp [UpperTheory.V.TR.oneL, UpperTheory.V.TR.toL])
  filter_upwards [hU.mem_nhds h1U, hinv, hunit, hdet] with x h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

def Dc (g : GA F 2) (x : UpperTheory.V.TR.Lie F 2) : ℂ := ((dl g x ^ ((1 : ℝ) / 2) : ℝ) : ℂ)

def Ac (g : GA F 2) (x : UpperTheory.V.TR.Lie F 2) : ℂ := (((dl g x)⁻¹ : ℝ) : ℂ)

def Sr (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (p : Pp F) (x : UpperTheory.V.TR.Lie F 2) : ℂ :=
  ∫ ξ, kap1 χ c g (p, ξ) * archS F (B1 (w1 g (p, ξ)) x) ∂(Measure.count : Measure (Xi F))

def Rc (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (p : Pp F) (z : UpperTheory.V.TR.Lie F 2) : ℂ :=
  ∫ ξ, kap2 χ c g (p, ξ) * archS F (B2 (w2 g (p, ξ)) z) ∂(Measure.count : Measure (Xi F))

theorem chart_eisInt_row (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (p : Pp F) :
    UpperTheory.V.TR.chart (fun g' => eisInt χ (Phi c) g' p.1 p.2) g =ᶠ[𝓝 (UpperTheory.V.TR.oneL F 2)]
      fun x => Dc g x * Sr χ c g p x := by
  filter_upwards [eventually_good g] with x ⟨_, _, hxu, hxd⟩
  set y : GL (Fin 2) (UpperTheory.V.TR.Rinf F) := (show IsUnit (Matrix.of x) from hxu).unit
  have hy : UpperTheory.V.TR.toL y.val = x := rfl
  rw [← hy, UpperTheory.V.TR.chart_val, eisInt_row, dl_eq g y hxd, Dc, Sr, integral_count_Xi, mul_comm]

theorem chart_eisInt_col (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) {C : ℂ}
    (hC : ∀ h : GA F 2, thetaS (Phi c) h = C * ((absD h)⁻¹ : ℝ) * thetaT (PhiH c) h) (p : Pp F) :
    UpperTheory.V.TR.chart (fun g' => eisInt χ (Phi c) g' p.1 p.2) g =ᶠ[𝓝 (UpperTheory.V.TR.oneL F 2)]
      fun x => (C * Ac g x * Dc g x) * Rc χ c g p (invL x) := by
  filter_upwards [eventually_good g] with x ⟨_, _, hxu, hxd⟩
  set y : GL (Fin 2) (UpperTheory.V.TR.Rinf F) := (show IsUnit (Matrix.of x) from hxu).unit
  have hy : UpperTheory.V.TR.toL y.val = x := rfl
  have hyi : UpperTheory.V.TR.toL (y⁻¹).val = invL x := by rw [← invL_val, hy]
  rw [← hy, UpperTheory.V.TR.chart_val, eisInt_col χ c g hC, dl_eq g y hxd, Ac, Dc, Rc, integral_count_Xi, hyi, hy]

theorem lie_derivative_eisenstein_integral {χ : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (hP : SPois) (H : Hyp χ c)
    (g : GA F 2) (X : UpperTheory.V.TR.Lie F 2) :
    Integrable (fun p : Pp F => UpperTheory.V.TR.lieD X (fun g' => eisInt χ (Phi c) g' p.1 p.2) g)
      (posRealMeasure.prod ((normOneMeasure F).restrict (normOneFundamentalDomain F))) ∧
    UpperTheory.V.TR.lieD X (Eis χ (Phi c)) g = ∫ p, UpperTheory.V.TR.lieD X (fun g' => eisInt χ (Phi c) g' p.1 p.2) g
      ∂(posRealMeasure.prod ((normOneMeasure F).restrict (normOneFundamentalDomain F))) := by
  obtain ⟨C, hC⟩ := hP F χ c H
  have hC' : ∀ h : GA F 2, thetaS (Phi c) h = C * ((absD h)⁻¹ : ℝ) * thetaT (PhiH c) h :=
    fun h => (hC h).2.2
  set one := UpperTheory.V.TR.oneL F 2 with hone
  set U : Set (UpperTheory.V.TR.Lie F 2) := Metric.ball one (1 / 4)
  have hU : IsOpen U := Metric.isOpen_ball
  have h1U : one ∈ U := Metric.mem_ball_self (by norm_num)
  have hc : (0 : ℝ) < 1 / 2 := by norm_num
  set S1 : Set {r : ℝ // 0 < r} := {t | 1 ≤ (t : ℝ)}
  set S2 : Set {r : ℝ // 0 < r} := {t | (t : ℝ) < 1}
  set ν := (normOneMeasure F).restrict (normOneFundamentalDomain F)
  set μ1 := (posRealMeasure.restrict S1).prod ν
  set μ2 := (posRealMeasure.restrict S2).prod ν
  have m1 := aestronglyMeasurable_first_kernel χ c g S1
  have mw1 := aestronglyMeasurable_row_weight (F := F) g S1
  have m2 := aestronglyMeasurable_second_kernel χ c g S2
  have mw2 := aestronglyMeasurable_column_weight (F := F) g S2
  obtain ⟨k1, hk1⟩ := hint1 H g m1 mw1
  obtain ⟨k2, hk2⟩ := hint2 H g m2 mw2
  have hB1 : ∀ x ∈ U, ∀ v, (1 / 2 : ℝ) * ‖v‖ ≤ ‖B1 v x‖ := fun x hx v => half_norm_le_norm_left_bilinear hx v
  have hB2 : ∀ x ∈ U, ∀ v, (1 / 2 : ℝ) * ‖v‖ ≤ ‖B2 v x‖ := fun x hx v => half_norm_le_norm_right_bilinear hx v
  set I1 : UpperTheory.V.TR.Lie F 2 → ℂ := fun x => ∫ q, kap1 χ c g q * archS F (B1 (w1 g q) x) ∂μS F S1
  set I2 : UpperTheory.V.TR.Lie F 2 → ℂ := fun z => ∫ q, kap2 χ c g q * archS F (B2 (w2 g q) z) ∂μS F S2
  set Sr' : Pp F → (UpperTheory.V.TR.Lie F 2 →L[ℝ] ℂ) := fun p =>
    ∫ ξ, kap1 χ c g (p, ξ) • fderiv ℝ (fun x => archS F (B1 (w1 g (p, ξ)) x)) one
      ∂(Measure.count : Measure (Xi F))
  set Rc' : Pp F → (UpperTheory.V.TR.Lie F 2 →L[ℝ] ℂ) := fun p =>
    ∫ ξ, kap2 χ c g (p, ξ) • fderiv ℝ (fun x => archS F (B2 (w2 g (p, ξ)) x)) one
      ∂(Measure.count : Measure (Xi F))
  have mk1 : ∀ p, AEStronglyMeasurable (fun ξ : Xi F => kap1 χ c g (p, ξ)) Measure.count := fun p =>
    ((measurable_first_kernel χ c g).comp measurable_prodMk_left).aestronglyMeasurable
  have mk2 : ∀ p, AEStronglyMeasurable (fun ξ : Xi F => kap2 χ c g (p, ξ)) Measure.count := fun p =>
    ((measurable_second_kernel χ c g).comp measurable_prodMk_left).aestronglyMeasurable
  have mv1 : ∀ p, AEStronglyMeasurable (fun ξ : Xi F => w1 g (p, ξ)) Measure.count := fun p =>
    ((measurable_row_weight g).comp measurable_prodMk_left).aestronglyMeasurable
  have mv2 : ∀ p, AEStronglyMeasurable (fun ξ : Xi F => w2 g (p, ξ)) Measure.count := fun p =>
    ((measurable_column_weight g).comp measurable_prodMk_left).aestronglyMeasurable
  have hk1' : Integrable (fun q => ‖kap1 χ c g q‖ * ((1 + ‖w1 g q‖) ^ k1)⁻¹) (μ1.prod Measure.count) := hk1
  have hk2' : Integrable (fun q => ‖kap2 χ c g q‖ * ((1 + ‖w2 g q‖) ^ k2)⁻¹) (μ2.prod Measure.count) := hk2
  have hder1 : ∀ᵐ p ∂μ1, HasFDerivAt (Sr χ c g p) (Sr' p) one := by
    filter_upwards [hk1'.prod_right_ae] with p hp
    exact hasFDerivAt_integral_schwartz_bilin (archS F) B1 hU hc hB1 (mk1 p) (mv1 p) hp h1U
  have hder2 : ∀ᵐ p ∂μ2, HasFDerivAt (Rc χ c g p) (Rc' p) one := by
    filter_upwards [hk2'.prod_right_ae] with p hp
    exact hasFDerivAt_integral_schwartz_bilin (archS F) B2 hU hc hB2 (mk2 p) (mv2 p) hp h1U
  have i1 : Integrable (fun q => kap1 χ c g q * archS F (B1 (w1 g q) one)) (μ1.prod Measure.count) :=
    integrable_schwartz_bilin (archS F) B1 hc hB1 m1 mw1 hk1 h1U
  have i2 : Integrable (fun q => kap2 χ c g q * archS F (B2 (w2 g q) one)) (μ2.prod Measure.count) :=
    integrable_schwartz_bilin (archS F) B2 hc hB2 m2 mw2 hk2 h1U
  have j1 : Integrable (fun q => kap1 χ c g q • fderiv ℝ (fun x => archS F (B1 (w1 g q) x)) one)
      (μ1.prod Measure.count) := integrable_fderiv_schwartz_bilin (archS F) B1 hc hB1 m1 mw1 hk1 h1U
  have j2 : Integrable (fun q => kap2 χ c g q • fderiv ℝ (fun x => archS F (B2 (w2 g q) x)) one)
      (μ2.prod Measure.count) := integrable_fderiv_schwartz_bilin (archS F) B2 hc hB2 m2 mw2 hk2 h1U
  have HI1 : HasFDerivAt I1 (∫ p, Sr' p ∂μ1) one :=
    (hasFDerivAt_integral_schwartz_bilin (archS F) B1 hU hc hB1 m1 mw1 hk1 h1U).congr_fderiv
      (integral_prod _ j1)
  have HI2 : HasFDerivAt I2 (∫ p, Rc' p ∂μ2) one :=
    (hasFDerivAt_integral_schwartz_bilin (archS F) B2 hU hc hB2 m2 mw2 hk2 h1U).congr_fderiv
      (integral_prod _ j2)
  have hH1 : I1 one = ∫ p, Sr χ c g p one ∂μ1 := integral_prod _ i1
  have hH2 : I2 one = ∫ p, Rc χ c g p one ∂μ2 := integral_prod _ i2

  have hdl := (contDiff_dl (F := F) g).contDiffAt (x := one)
  have hdl0 : dl g one ≠ 0 := by rw [dl_one]; exact (absD_pos g).ne'
  have hD : ContDiffAt ℝ ∞ (Dc g) one :=
    (Complex.ofRealCLM.contDiff.contDiffAt).comp _ (hdl.rpow_const_of_ne hdl0)
  have hA : ContDiffAt ℝ ∞ (Ac g) one :=
    (Complex.ofRealCLM.contDiff.contDiffAt).comp _ (hdl.inv hdl0)
  have hA2 : ContDiffAt ℝ ∞ (fun x => C * Ac g x * Dc g x) one := (contDiffAt_const.mul hA).mul hD
  have hDa := (hD.differentiableAt (by simp)).hasFDerivAt
  have hA2a := (hA2.differentiableAt (by simp)).hasFDerivAt
  have hinva := (contDiffAt_invL (F := F).differentiableAt (by simp)).hasFDerivAt
  obtain ⟨L1int, L1diff, L1eq⟩ := fderiv_mul_comp_integral hder1 j1.integral_prod_left i1.integral_prod_left
    HI1 hH1 hDa (hasFDerivAt_id one) rfl X
  obtain ⟨L2int, L2diff, L2eq⟩ := fderiv_mul_comp_integral hder2 j2.integral_prod_left i2.integral_prod_left
    HI2 hH2 hA2a hinva invL_one X
  simp only [id] at L1int L1diff L1eq

  have eL1 : (fun p : Pp F => UpperTheory.V.TR.lieD X (fun g' => eisInt χ (Phi c) g' p.1 p.2) g) =
      fun p => fderiv ℝ (fun x => Dc g x * Sr χ c g p x) one X := by
    funext p
    rw [UpperTheory.V.TR.lieD, (chart_eisInt_row χ c g p).fderiv_eq]
  have eL2 : (fun p : Pp F => UpperTheory.V.TR.lieD X (fun g' => eisInt χ (Phi c) g' p.1 p.2) g) =
      fun p => fderiv ℝ (fun x => (C * Ac g x * Dc g x) * Rc χ c g p (invL x)) one X := by
    funext p
    rw [UpperTheory.V.TR.lieD, (chart_eisInt_col χ c g hC' p).fderiv_eq]

  have hs : MeasurableSet (S1 ×ˢ (Set.univ : Set (normOneSubgroup F))) :=
    measurableSet_ge_one.prod MeasurableSet.univ
  have hμ1 : (posRealMeasure.prod ν).restrict (S1 ×ˢ Set.univ) = μ1 := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hμ2 : (posRealMeasure.prod ν).restrict (S1 ×ˢ (Set.univ : Set (normOneSubgroup F)))ᶜ = μ2 := by
    have e : (S1 ×ˢ (Set.univ : Set (normOneSubgroup F)))ᶜ = S2 ×ˢ Set.univ := by
      ext p
      simp [S1, S2]
    rw [e, ← Measure.prod_restrict, Measure.restrict_univ]
  have hint : Integrable (fun p : Pp F => UpperTheory.V.TR.lieD X (fun g' => eisInt χ (Phi c) g' p.1 p.2) g)
      (posRealMeasure.prod ν) := by
    have h1 : IntegrableOn (fun p : Pp F => UpperTheory.V.TR.lieD X (fun g' => eisInt χ (Phi c) g' p.1 p.2) g)
        (S1 ×ˢ Set.univ) (posRealMeasure.prod ν) := by
      rw [IntegrableOn, hμ1, eL1]
      exact L1int
    have h2 : IntegrableOn (fun p : Pp F => UpperTheory.V.TR.lieD X (fun g' => eisInt χ (Phi c) g' p.1 p.2) g)
        (S1 ×ˢ Set.univ)ᶜ (posRealMeasure.prod ν) := by
      rw [IntegrableOn, hμ2, eL2]
      exact L2int
    have := h1.union h2
    rwa [Set.union_compl_self, integrableOn_univ] at this
  refine ⟨hint, ?_⟩
  rw [← integral_add_compl hs hint, hμ1, hμ2]

  have hev : UpperTheory.V.TR.chart (Eis χ (Phi c)) g =ᶠ[𝓝 one]
      fun x => Dc g x * I1 x + (C * Ac g x * Dc g x) * I2 (invL x) := by
    filter_upwards [eventually_good g] with x ⟨hxU, hxi, hxu, hxd⟩
    set y : GL (Fin 2) (UpperTheory.V.TR.Rinf F) := (show IsUnit (Matrix.of x) from hxu).unit
    have hy : UpperTheory.V.TR.toL y.val = x := rfl
    have hyi : UpperTheory.V.TR.toL (y⁻¹).val = invL x := by rw [← invL_val, hy]
    have hyd : absD (g * UpperTheory.V.TR.infGL F 2 y) = dl g x := by rw [dl_eq g y hxd, hy]
    have i1x := integrable_schwartz_bilin (archS F) B1 hc hB1 m1 mw1 hk1 hxU
    have i2x := integrable_schwartz_bilin (archS F) B2 hc hB2 m2 mw2 hk2 hxi
    rw [← hy] at i1x
    rw [← hyi] at i2x
    rw [← hy, UpperTheory.V.TR.chart_val, eis_decomp χ c g hC' y i1x i2x, hyd, hyi, hy, Dc, Ac]
  have hsum : HasFDerivAt (fun x => Dc g x * I1 x + C * Ac g x * Dc g x * I2 (invL x)) _ one :=
    L1diff.hasFDerivAt.add L2diff.hasFDerivAt
  rw [UpperTheory.V.TR.lieD, hev.fderiv_eq, hsum.fderiv, ContinuousLinearMap.add_apply, ← L1diff.hasFDerivAt.fderiv,
    ← L2diff.hasFDerivAt.fderiv, L1eq, L2eq]
  congr 1
  · congr 1
    funext p
    exact (congrFun eL1 p).symm
  · congr 1
    funext p
    exact (congrFun eL2 p).symm

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

namespace UpperTheory.HilbertEisensteinWeightOne

theorem lieD_Eis_eq_integral {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {χ : HChar F}
    {c : HeightOneSpectrum (𝓞 F) → ℕ} (hP : SPois) (_hI : SInt) (H : Hyp χ c) (g : GA F 2) (X : UpperTheory.V.TR.Lie F 2) :
    Integrable (fun p : {r : ℝ // 0 < r} × normOneSubgroup F => UpperTheory.V.TR.lieD X (fun g' => eisInt χ (Phi c) g' p.1 p.2) g)
      (posRealMeasure.prod ((normOneMeasure F).restrict (normOneFundamentalDomain F))) ∧
    UpperTheory.V.TR.lieD X (Eis χ (Phi c)) g = ∫ p, UpperTheory.V.TR.lieD X (fun g' => eisInt χ (Phi c) g' p.1 p.2) g
      ∂(posRealMeasure.prod ((normOneMeasure F).restrict (normOneFundamentalDomain F))) :=
  EisensteinSmoothness.lie_derivative_eisenstein_integral hP H g X

end UpperTheory.HilbertEisensteinWeightOne
