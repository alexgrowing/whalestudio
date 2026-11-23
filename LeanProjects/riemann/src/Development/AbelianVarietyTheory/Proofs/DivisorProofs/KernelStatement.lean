import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformDerivativeApproxStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerFormCompactBoundsStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory MeasureTheory Set Metric
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.L2DbarEstimates GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ChernReg

namespace GlobalTheory.KernelBd

section Flat

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_det_ge [FiniteDimensional ℝ E] : ∃ ε > 0, ∀ L : E →L[ℝ] E,
    ‖L - ContinuousLinearMap.id ℝ E‖ ≤ ε → 1 / 2 ≤ |L.det| := by
  have hc : ContinuousAt (fun L : E →L[ℝ] E => L.det) (ContinuousLinearMap.id ℝ E) :=
    ContinuousLinearMap.continuous_det.continuousAt
  rw [Metric.continuousAt_iff] at hc
  obtain ⟨ε, hε, h⟩ := hc (1 / 2) (by norm_num)
  refine ⟨ε / 2, by positivity, fun L hL => ?_⟩
  have h1 := h (x := L) (by rw [dist_eq_norm]; linarith)
  have hid : (ContinuousLinearMap.id ℝ E).det = 1 := LinearMap.det_id
  rw [Real.dist_eq, hid] at h1
  linarith [le_abs_self L.det, (abs_sub_lt_iff.1 h1).2]

theorem injOn_of_near_id {g : E → E} {r : ℝ} {L : E → E →L[ℝ] E}
    (hg : ∀ η ∈ closedBall (0 : E) r, HasFDerivAt g (L η) η)
    (hL : ∀ η ∈ closedBall (0 : E) r, ‖L η - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2) :
    InjOn g (closedBall 0 r) ∧ ∀ η ∈ closedBall (0 : E) r, ‖g η - g 0‖ ≤ 2 * ‖η‖ := by
  have hb : ∀ η ∈ closedBall (0 : E) r, HasFDerivWithinAt (fun x => g x - x)
      (L η - ContinuousLinearMap.id ℝ E) (closedBall 0 r) η :=
    fun η hη => ((hg η hη).sub (hasFDerivAt_id η)).hasFDerivWithinAt
  have hmv : ∀ x ∈ closedBall (0 : E) r, ∀ y ∈ closedBall (0 : E) r,
      ‖(g y - y) - (g x - x)‖ ≤ 1 / 2 * ‖y - x‖ :=
    fun x hx y hy => (convex_closedBall 0 r).norm_image_sub_le_of_norm_hasFDerivWithin_le hb hL hx hy
  refine ⟨fun x hx y hy hxy => ?_, fun η hη => ?_⟩
  · have h := hmv x hx y hy
    rw [hxy] at h
    have e : (g y - y) - (g y - x) = -(y - x) := by abel
    rw [e, norm_neg] at h
    have h0 : ‖y - x‖ = 0 := by linarith [norm_nonneg (y - x)]
    exact (sub_eq_zero.1 (norm_eq_zero.1 h0)).symm
  · have hr : 0 ≤ r := (norm_nonneg η).trans (mem_closedBall_zero_iff.1 hη)
    have h := hmv 0 (mem_closedBall_self hr) η hη
    have e : g η - g 0 = ((g η - η) - (g 0 - 0)) + η := by abel
    rw [e]
    calc _ ≤ ‖(g η - η) - (g 0 - 0)‖ + ‖η‖ := norm_add_le _ _
      _ ≤ 1 / 2 * ‖η - 0‖ + ‖η‖ := by gcongr
      _ ≤ 2 * ‖η‖ := by rw [sub_zero]; linarith [norm_nonneg η]

theorem unif_fderiv [FiniteDimensional ℝ E] (F : E × E → E) (U : Set (E × E)) (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 F U) (K : Set E) (hK : IsCompact K) (hKU : ∀ z ∈ K, (z, (0 : E)) ∈ U)
    (h1 : ∀ z ∈ K, ∀ η : E, HasDerivAt (fun s : ℝ => F (z, s • η)) η 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∃ L : E → E → E →L[ℝ] E, ∀ z ∈ K, ∀ η : E, ‖η‖ ≤ δ → (z, η) ∈ U ∧
      HasFDerivAt (fun η' => F (z, η')) (L z η) η ∧ ‖L z η - ContinuousLinearMap.id ℝ E‖ ≤ ε :=
  GlobalTheory.T.uniform_derivative_approx F U hU hF K hK hKU h1 ε hε

theorem cov_bound [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {s : Set E} (hs : MeasurableSet s) {Φ : E → E} {Φ' : E → E →L[ℝ] E}
    (hΦ : ∀ x ∈ s, HasFDerivWithinAt Φ (Φ' x) s x) (hinj : InjOn Φ s) {δ : ℝ} (hδ : 0 < δ)
    (hdet : ∀ x ∈ s, δ ≤ |(Φ' x).det|) {g : E → ℝ} (hg : IntegrableOn g (Φ '' s) μ) :
    IntegrableOn (g ∘ Φ) s μ ∧ ∫ x in s, |g (Φ x)| ∂μ ≤ δ⁻¹ * ∫ x in Φ '' s, |g x| ∂μ := by
  have hI := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ hs hΦ hinj g).1 hg
  have hIa := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ hs hΦ hinj
    (fun x => |g x|)).1 hg.abs
  have hm : AEMeasurable (fun x => |(Φ' x).det|⁻¹) (μ.restrict s) :=
    (continuous_abs.measurable.comp_aemeasurable
      (ContinuousLinearMap.continuous_det.measurable.comp_aemeasurable (aemeasurable_fderivWithin μ hs hΦ))).inv
  have hgi : IntegrableOn (g ∘ Φ) s μ := by
    have h := hI.bdd_mul (c := δ⁻¹) hm.aestronglyMeasurable ((ae_restrict_iff' hs).2 (ae_of_all _ fun x hx => by
      rw [norm_inv, Real.norm_eq_abs, abs_abs]
      exact inv_anti₀ hδ (hdet x hx)))
    refine IntegrableOn.congr_fun h (fun x hx => ?_) hs
    have h0 : |(Φ' x).det| ≠ 0 := (hδ.trans_le (hdet x hx)).ne'
    simp only [smul_eq_mul, Function.comp_apply]
    field_simp
  refine ⟨hgi, ?_⟩
  rw [integral_image_eq_integral_abs_det_fderiv_smul μ hs hΦ hinj, ← integral_const_mul]
  refine setIntegral_mono_on hgi.abs (hIa.const_mul δ⁻¹) hs fun x hx => ?_
  have h1 : 1 ≤ δ⁻¹ * |(Φ' x).det| := by
    rw [inv_mul_eq_div, one_le_div hδ]
    exact hdet x hx
  simp only [smul_eq_mul, Function.comp_apply]
  nlinarith [abs_nonneg (g (Φ x))]

end Flat

theorem cutoff_ge {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 4) : Real.exp (-(4 / 3)) ≤ ChernReg.cutoff s := by
  have hs : s < 1 := by linarith
  rw [ChernReg.cutoff, if_pos hs]
  have ha : 1 ≤ ((1 - s) ^ 2)⁻¹ := (one_le_inv₀ (by nlinarith)).2 (by nlinarith)
  have hb : Real.exp (-(4 / 3)) ≤ Real.exp (s - 1)⁻¹ := by
    apply Real.exp_le_exp.2
    have e : (s - 1)⁻¹ = -(1 - s)⁻¹ := by rw [← neg_sub, inv_neg]
    have h2 : (1 - s)⁻¹ ≤ (3 / 4)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
    rw [e]
    norm_num at h2 ⊢
    linarith
  calc Real.exp (-(4 / 3)) ≤ Real.exp (s - 1)⁻¹ := hb
    _ = 1 * Real.exp (s - 1)⁻¹ := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right ha (Real.exp_pos _).le

theorem form_comparable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}
    {R : AnRead p σ d} {a : ChartForm p σ d} (ha : IsKaehlerForm R a) (c : AlgChart p σ d) {Kc : Set (V d)}
    (hK : IsCompact Kc) (hKt : Kc ⊆ c.e.target) : ∃ m M : ℝ, 0 < m ∧ 0 < M ∧
      ∀ y ∈ c.e.source, c.e y ∈ Kc → ∀ v : V d, m * ‖v‖ ^ 2 ≤ a c y v.ofLp ∧ a c y v.ofLp ≤ M * ‖v‖ ^ 2 :=
  GlobalTheory.T.kaehler_form_compact_bounds ha c hK hKt

end GlobalTheory.KernelBd

namespace GlobalTheory.HeightParts
open GlobalTheory.KernelBd

set_option maxHeartbeats 1000000 in
theorem kernelSt_holds : KernelSt := by
  intro k _ Y p σ d _ a E ha hE c Kc hK hKt
  obtain ⟨F, hFd⟩ : ∃ F : V d × V d → V d, F = fun q => c.e (E c (c.e.symm q.1) q.2.ofLp) := ⟨_, rfl⟩
  obtain ⟨U, hUd⟩ : ∃ U : Set (V d × V d),
      U = {q | q.1 ∈ c.e.target ∧ E c (c.e.symm q.1) q.2.ofLp ∈ c.e.source} := ⟨_, rfl⟩
  have hUo : IsOpen U := by
    have h := (hE.cont c).isOpen_inter_preimage (c.e.open_target.prod isOpen_univ) c.e.open_source
    convert h using 1
    ext q
    simp [hUd, Set.mem_prod]
  have hFc : ContDiffOn ℝ 1 F U := hFd ▸ hUd ▸ (hE.smooth c c).of_le (by exact_mod_cast le_top)
  have hKU : ∀ z ∈ Kc, (z, (0 : V d)) ∈ U := fun z hz => by
    rw [hUd]
    refine ⟨hKt hz, ?_⟩
    simp only [WithLp.ofLp_zero]
    rw [hE.zero c _ (c.e.map_target (hKt hz))]
    exact c.e.map_target (hKt hz)
  have h1 : ∀ z ∈ Kc, ∀ η : V d, HasDerivAt (fun s : ℝ => F (z, s • η)) η 0 := by
    intro z hz η
    have hz' := c.e.map_target (hKt hz)
    have hd : DifferentiableAt ℝ F (z, 0) :=
      (hFc.differentiableOn one_ne_zero _ (hKU z hz)).differentiableAt (hUo.mem_nhds (hKU z hz))
    have hl : DifferentiableAt ℝ (fun s : ℝ => ((z, s • η) : V d × V d)) 0 :=
      (differentiableAt_const _).prodMk (differentiableAt_id.smul_const η)
    have hd' : DifferentiableAt ℝ (fun s : ℝ => F (z, s • η)) 0 := by
      have hd0 : DifferentiableAt ℝ F ((fun s : ℝ => ((z, s • η) : V d × V d)) 0) := by simpa using hd
      exact hd0.comp (0 : ℝ) hl
    have hj := hE.jets c (c.e.symm z) hz' η 1
    simp only [iteratedDeriv_one, jet_one] at hj
    have e : (fun s : ℝ => F (z, s • η)) = fun t => c.e (E c (c.e.symm z) (t • η.ofLp)) := by
      funext s
      simp [hFd]
    have h := hd'.hasDerivAt
    rwa [show deriv (fun s : ℝ => F (z, s • η)) 0 = η by rw [e]; exact hj] at h
  obtain ⟨m, M, hm, hM, hmM⟩ := form_comparable ha c hK hKt
  obtain ⟨ε₀, hε₀, hdet⟩ := exists_det_ge (E := V d)
  obtain ⟨δ, hδ, L, hL⟩ := unif_fderiv F U hUo hFc Kc hK hKU h1 (min ε₀ (1 / 2)) (by positivity)
  obtain ⟨ρ, hρ, hρt⟩ := hK.exists_cthickening_subset_open c.e.open_target hKt

  set R : ℝ := 1 + m⁻¹ with hRdef
  have hR : 0 < R := by positivity
  have hball : ∀ y ∈ c.e.source, c.e y ∈ Kc → ∀ v : V d, a c y v.ofLp < 1 → ‖v‖ ≤ R := by
    intro y hy hz v hv
    have h := (hmM y hy hz v).1
    by_contra hc
    push_neg at hc
    have h2 : 1 ≤ ‖v‖ := by have : 0 < m⁻¹ := by positivity
                            linarith
    have h3 : m * ‖v‖ > 1 := by
      have : m * (1 + m⁻¹) = m + 1 := by field_simp
      nlinarith
    nlinarith
  set r₀ : ℝ := (2 * (M + 1))⁻¹ with hr₀def
  have hr₀ : 0 < r₀ := by positivity
  set mm : ℝ := Real.exp (-(4 / 3)) * (volume (ball (0 : V d) r₀)).toReal with hmmdef
  have hmm : 0 < mm := mul_pos (Real.exp_pos _)
    (ENNReal.toReal_pos (measure_ball_pos volume _ hr₀).ne' measure_ball_lt_top.ne)
  set C : ℝ := max (2 * R + 1) (4 / mm) with hCdef
  have hC : 0 < C := lt_max_of_lt_left (by positivity)
  refine ⟨C, min (δ / R) (ρ / C), hC, by positivity, ?_⟩
  intro y hy hyK t ht htt
  have hyz : c.e.symm (c.e y) = y := c.e.left_inv hy
  have hCt : C * t ≤ ρ := by
    have := htt.trans (min_le_right _ _)
    rwa [le_div_iff₀ hC, mul_comm] at this
  have hRt : t * R ≤ δ := by
    have := htt.trans (min_le_left _ _)
    rwa [le_div_iff₀ hR] at this

  have hg : ∀ η ∈ closedBall (0 : V d) δ, HasFDerivAt (fun η' => F (c.e y, η')) (L (c.e y) η) η :=
    fun η hη => (hL (c.e y) hyK η (mem_closedBall_zero_iff.1 hη)).2.1
  have hgL : ∀ η ∈ closedBall (0 : V d) δ, ‖L (c.e y) η - ContinuousLinearMap.id ℝ (V d)‖ ≤ 1 / 2 :=
    fun η hη => (hL (c.e y) hyK η (mem_closedBall_zero_iff.1 hη)).2.2.trans (min_le_right _ _)
  obtain ⟨hinj, hnorm⟩ := injOn_of_near_id hg hgL
  have hF0 : F (c.e y, 0) = c.e y := by
    simp only [hFd, WithLp.ofLp_zero, hyz, hE.zero c y hy]
  have hFy : ∀ v : V d, ‖v‖ ≤ R → E c y (t • v.ofLp) ∈ c.e.source ∧
      F (c.e y, t • v) = c.e (E c y (t • v.ofLp)) ∧ c.e (E c y (t • v.ofLp)) ∈ ball (c.e y) (C * t) := by
    intro v hv
    have htv : ‖t • v‖ ≤ δ := by
      rw [norm_smul, Real.norm_of_nonneg ht.le]
      nlinarith
    have hU' := (hL (c.e y) hyK (t • v) htv).1
    rw [hUd] at hU'
    have eF : F (c.e y, t • v) = c.e (E c y (t • v.ofLp)) := by simp [hFd, hyz]
    refine ⟨by simpa [hyz] using hU'.2, eF, ?_⟩
    rw [mem_ball, dist_eq_norm, ← eF]
    have := hnorm (t • v) (mem_closedBall_zero_iff.2 htv)
    rw [hF0, norm_smul, Real.norm_of_nonneg ht.le] at this
    have h2 : 2 * (t * ‖v‖) < C * t := by
      have : 2 * R + 1 ≤ C := le_max_left _ _
      nlinarith
    linarith
  refine ⟨?_, fun ξ hξ => ?_, fun f hf => ?_⟩
  · intro w hw
    apply hρt
    exact cthickening_mono hCt Kc (closedBall_subset_cthickening hyK _ (ball_subset_closedBall hw))
  · have hv : ‖(WithLp.toLp 2 ξ : V d)‖ ≤ R := hball y hy hyK _ (by simpa using hξ)
    obtain ⟨h1', -, h3'⟩ := hFy _ hv
    simp only [WithLp.ofLp_toLp] at h1' h3'
    exact ⟨h1', h3'⟩
  obtain ⟨hac, hah⟩ := continuous_and_smul ha hy
  obtain ⟨s, hsdef⟩ : ∃ s : Set (V d), s = {v | a c y v.ofLp < 1} := ⟨_, rfl⟩
  have hso : IsOpen s := hsdef ▸ isOpen_lt (hac.comp (PiLp.continuous_ofLp 2 _)) continuous_const
  have hsR : s ⊆ closedBall 0 R := fun v hv => mem_closedBall_zero_iff.2 (hball y hy hyK v (by rw [hsdef] at hv; exact hv))
  obtain ⟨Φ, hΦd⟩ : ∃ Φ : V d → V d, Φ = fun v => F (c.e y, t • v) := ⟨_, rfl⟩
  obtain ⟨Φ', hΦ'd⟩ : ∃ Φ' : V d → V d →L[ℝ] V d, Φ' = fun v => t • L (c.e y) (t • v) := ⟨_, rfl⟩
  have htv : ∀ v ∈ closedBall (0 : V d) R, t • v ∈ closedBall (0 : V d) δ := fun v hv => by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg ht.le]
    rw [mem_closedBall_zero_iff] at hv
    nlinarith
  have hΦ : ∀ v ∈ closedBall (0 : V d) R, HasFDerivAt Φ (Φ' v) v := fun v hv => by
    have h := (hg _ (htv v hv)).comp v ((hasFDerivAt_id v).const_smul t)
    have e1 : Φ = (fun η' => F (c.e y, η')) ∘ fun v => t • id v := by rw [hΦd]; rfl
    rw [e1]
    refine h.congr_fderiv ?_
    rw [hΦ'd]
    ext w
    simp
  have hinjΦ : InjOn Φ s := fun v₁ h₁ v₂ h₂ he =>
    smul_right_injective (V d) ht.ne' (hinj (htv _ (hsR h₁)) (htv _ (hsR h₂)) (by rw [hΦd] at he; exact he))
  have hfin : Module.finrank ℝ (V d) = 2 * d := by
    rw [GlobalTheory.finrank_real_euclideanSpace_complex, Fintype.card_fin]
  have hdetΦ : ∀ v ∈ s, t ^ (2 * d) / 2 ≤ |(Φ' v).det| := fun v hv => by
    have h2 := hdet _ ((hL (c.e y) hyK _ (mem_closedBall_zero_iff.1 (htv v (hsR hv)))).2.2.trans (min_le_left _ _))
    have e : (Φ' v).det = t ^ (2 * d) * (L (c.e y) (t • v)).det := by
      rw [hΦ'd]
      simp only [ContinuousLinearMap.det, ContinuousLinearMap.coe_smul, LinearMap.det_smul, hfin]
    rw [e, abs_mul, abs_of_pos (by positivity : (0:ℝ) < t ^ (2 * d))]
    nlinarith [pow_pos ht (2 * d)]
  have himg : Φ '' s ⊆ ball (c.e y) (C * t) := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨-, e, h⟩ := hFy v (mem_closedBall_zero_iff.1 (hsR hv))
    rw [hΦd]
    simpa [e] using h
  have hsymm : ∀ v ∈ s, (f ∘ c.e.symm) (Φ v) = f (E c y (t • v.ofLp)) := fun v hv => by
    obtain ⟨h1, e, -⟩ := hFy v (mem_closedBall_zero_iff.1 (hsR hv))
    rw [hΦd]
    simp only [Function.comp_apply, e, c.e.left_inv h1]
  obtain ⟨hI, hB⟩ := cov_bound volume hso.measurableSet (fun v hv => (hΦ v (hsR hv)).hasFDerivWithinAt)
    hinjΦ (by positivity : (0:ℝ) < t ^ (2 * d) / 2) hdetΦ (hf.mono_set himg)
  let eV : V d ≃ᵐ (Fin d → ℂ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℂ)).toHomeomorph.toMeasurableEquiv
  have hV : MeasurePreserving eV volume volume := GlobalTheory.volume_preserving_ofLp_complex (Fin d)
  obtain ⟨H, hHdef⟩ : ∃ H : V d → ℝ, H = fun v => f (E c y (t • v.ofLp)) * ChernReg.cutoff (a c y v.ofLp) :=
    ⟨_, rfl⟩
  have hHs : Function.support H ⊆ s := fun v hv => by
    by_contra h
    rw [hsdef] at h
    exact hv (by simp [hHdef, ChernReg.cutoff, show ¬ a c y v.ofLp < 1 from h])
  have hcm : Measurable fun v : V d => ChernReg.cutoff (a c y v.ofLp) :=
    measurable_cutoff.comp (hac.comp (PiLp.continuous_ofLp 2 _)).measurable
  have hHi : Integrable H := by
    refine (integrableOn_iff_integrable_of_support_subset hHs).1 ?_
    have h := hI.mul_bdd (c := 2) hcm.aestronglyMeasurable (ae_of_all _ fun v => by
      rw [Real.norm_of_nonneg (cutoff_nonneg _)]; exact cutoff_le _)
    refine IntegrableOn.congr_fun h (fun v hv => ?_) hso.measurableSet
    show ((f ∘ c.e.symm) ∘ Φ) v * _ = H v
    rw [Function.comp_apply, hsymm v hv, hHdef]
  have hint : Integrable fun ξ : Fin d → ℂ => f (E c y (t • ξ)) * ChernReg.cutoff (a c y ξ) :=
    (hV.integrable_comp_emb eV.measurableEmbedding).1 (by rw [hHdef] at hHi; exact hHi)
  refine ⟨hint, ?_⟩
  have hci : Integrable fun v : V d => ChernReg.cutoff (a c y v.ofLp) :=
    (hV.integrable_comp_emb eV.measurableEmbedding).2 (integrable_cutoff hac hah (ha.2 c y hy))
  have heV : ∀ v : V d, eV v = v.ofLp := fun v => rfl
  have hmass : mm ≤ ∫ ξ, ChernReg.cutoff (a c y ξ) := by
    rw [← hV.integral_comp' (fun ξ => ChernReg.cutoff (a c y ξ))]
    simp only [heV]
    calc mm ≤ ∫ v in ball (0 : V d) r₀, ChernReg.cutoff (a c y v.ofLp) := by
          rw [hmmdef, mul_comm]
          refine setIntegral_ge_of_const_le measurableSet_ball measure_ball_lt_top.ne (fun v hv => ?_)
            hci.integrableOn
          have hv' : ‖v‖ < r₀ := mem_ball_zero_iff.1 hv
          have hb := hmM y hy hyK v
          have hr : 2 * (M + 1) * r₀ = 1 := by rw [hr₀def]; field_simp
          refine cutoff_ge (le_trans (by positivity) hb.1) (hb.2.trans ?_)
          have h4 : (2 * (M + 1) * ‖v‖) ^ 2 ≤ 1 := by
            have : 2 * (M + 1) * ‖v‖ ≤ 1 := (mul_le_mul_of_nonneg_left hv'.le (by positivity)).trans hr.le
            exact pow_le_one₀ (by positivity) this
          have h5 : (2 * (M + 1) * ‖v‖) ^ 2 = 4 * ((M + 1) ^ 2 * ‖v‖ ^ 2) := by ring
          have h6 : M * ‖v‖ ^ 2 ≤ (M + 1) ^ 2 * ‖v‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
          linarith
      _ ≤ _ := setIntegral_le_integral hci (ae_of_all _ fun _ => cutoff_nonneg _)
  have hmpos : 0 < ∫ ξ, ChernReg.cutoff (a c y ξ) := hmm.trans_le hmass
  have hIb : 0 ≤ ∫ v in ball (c.e y) (C * t), |f (c.e.symm v)| := setIntegral_nonneg measurableSet_ball fun _ _ => abs_nonneg _
  have hnum : |∫ ξ, f (E c y (t • ξ)) * ChernReg.cutoff (a c y ξ)| ≤
      4 / t ^ (2 * d) * ∫ v in ball (c.e y) (C * t), |f (c.e.symm v)| := by
    rw [← hV.integral_comp' (fun ξ : Fin d → ℂ => f (E c y (t • ξ)) * ChernReg.cutoff (a c y ξ))]
    simp only [heV]
    rw [← hHdef]
    calc |∫ v, H v| ≤ ∫ v, |H v| := abs_integral_le_integral_abs
      _ = ∫ v in s, |H v| := (setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => by
          have : H v = 0 := Function.notMem_support.1 fun h => hv (hHs h)
          rw [this, abs_zero]).symm
      _ ≤ ∫ v in s, 2 * |(f ∘ c.e.symm) (Φ v)| := by
          refine setIntegral_mono_on hHi.abs.integrableOn (hI.abs.const_mul 2) hso.measurableSet fun v hv => ?_
          rw [hsymm v hv, hHdef]
          simp only [abs_mul, abs_of_nonneg (cutoff_nonneg _)]
          nlinarith [cutoff_le (a c y v.ofLp), abs_nonneg (f (E c y (t • v.ofLp)))]
      _ = 2 * ∫ v in s, |(f ∘ c.e.symm) (Φ v)| := integral_const_mul _ _
      _ ≤ 2 * ((t ^ (2 * d) / 2)⁻¹ * ∫ v in Φ '' s, |(f ∘ c.e.symm) v|) := by gcongr
      _ ≤ 2 * ((t ^ (2 * d) / 2)⁻¹ * ∫ v in ball (c.e y) (C * t), |f (c.e.symm v)|) := by
          gcongr
          exact setIntegral_mono_set hf.abs (ae_of_all _ fun _ => abs_nonneg _) himg.eventuallyLE
      _ = 4 / t ^ (2 * d) * ∫ v in ball (c.e y) (C * t), |f (c.e.symm v)| := by
          field_simp
          ring
  rw [rho_eq ha hE f hy t, rhoIn, mean, abs_div, abs_of_pos hmpos]
  calc _ ≤ (4 / t ^ (2 * d) * ∫ v in ball (c.e y) (C * t), |f (c.e.symm v)|) / mm := by
        refine (div_le_div_of_nonneg_right hnum hmpos.le).trans ?_
        exact div_le_div_of_nonneg_left (by positivity) hmm hmass
    _ = 4 / mm / t ^ (2 * d) * ∫ v in ball (c.e y) (C * t), |f (c.e.symm v)| := by ring
    _ ≤ _ := by
        gcongr
        exact le_max_right _ _

end GlobalTheory.HeightParts
