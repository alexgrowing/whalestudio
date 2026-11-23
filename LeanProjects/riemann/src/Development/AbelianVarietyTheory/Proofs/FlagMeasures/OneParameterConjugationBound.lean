import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBasis
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryRepMatrixCoefficientBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarSubgroupBiInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalVolumeGrowthStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.TorusLip

lemma sq_integral_le {r : ℝ → ℝ} (hr : Continuous r) :
    (∫ t in (0:ℝ)..1, r t) ^ 2 ≤ ∫ t in (0:ℝ)..1, r t ^ 2 := by
  set a := ∫ t in (0:ℝ)..1, r t with ha
  have h1 : IntervalIntegrable r MeasureTheory.volume 0 1 := hr.intervalIntegrable 0 1
  have h2 : IntervalIntegrable (fun t => r t ^ 2) MeasureTheory.volume 0 1 :=
    (hr.pow 2).intervalIntegrable 0 1
  have hnn : 0 ≤ ∫ t in (0:ℝ)..1, (r t - a) ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun t _ => sq_nonneg _)
  have e : ∀ t, (r t - a) ^ 2 = r t ^ 2 - (2 * a * r t - a ^ 2) := fun t => by ring
  simp_rw [e] at hnn
  rw [intervalIntegral.integral_sub h2 ((h1.const_mul (2 * a)).sub intervalIntegrable_const),
    intervalIntegral.integral_sub (h1.const_mul (2 * a)) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hnn
  simp only [sub_zero, one_smul, smul_eq_mul, one_mul] at hnn
  nlinarith

lemma torus_lipschitz_l2_bound {G ι : Type} [Fintype ι] [TopologicalSpace G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [SFinite μ] (β : G → ℝ) (hβ : Measurable β) (hβ0 : ∀ g, 0 ≤ β g)
    (Φ : ι → ℝ → G → ℂ) (hΦ : ∀ i, Continuous fun p : ℝ × G => Φ i p.1 p.2) (D : G → ℂ) (M s : ℝ) (hM : 0 ≤ M)
    (hs : |s| ≤ 1) (B : ι → ℝ)
    (hD : ∀ g, ∃ y : ι → ℝ, ∑ i, y i ^ 2 ≤ M ∧ D g = ∫ t in (0:ℝ)..s, ∑ i, (y i : ℂ) * Φ i t g)
    (hB : ∀ i t, |t| ≤ 1 → Integrable (fun g => β g * ‖Φ i t g‖ ^ 2) μ ∧ ∫ g, β g * ‖Φ i t g‖ ^ 2 ∂μ ≤ B i) :
    ∫ g, β g * ‖D g‖ ^ 2 ∂μ ≤ M * s ^ 2 * ∑ i, B i := by
  set q : ι → G → ℝ := fun i g => ∫ u in (0:ℝ)..1, β g * ‖Φ i (s * u) g‖ ^ 2 with hqdef
  have hΦc : ∀ i g, Continuous fun u : ℝ => Φ i (s * u) g := fun i g =>
    (hΦ i).comp ((continuous_const.mul continuous_id).prodMk continuous_const)
  have hpt : ∀ g, β g * ‖D g‖ ^ 2 ≤ M * s ^ 2 * ∑ i, q i g := by
    intro g
    obtain ⟨y, hy, hDg⟩ := hD g
    set F : ℝ → ℂ := fun t => ∑ i, (y i : ℂ) * Φ i t g with hF
    have hFc : Continuous F := continuous_finset_sum _ (fun i _ =>
      continuous_const.mul ((hΦ i).comp (continuous_id.prodMk continuous_const)))
    have hFs : Continuous fun u : ℝ => F (s * u) := hFc.comp (continuous_const.mul continuous_id)
    have hD' : D g = s • ∫ u in (0:ℝ)..1, F (s * u) := by
      rw [hDg, intervalIntegral.smul_integral_comp_mul_left, mul_zero, mul_one]
    have h1 : ‖D g‖ ^ 2 ≤ s ^ 2 * ∫ u in (0:ℝ)..1, ‖F (s * u)‖ ^ 2 := by
      have hn : ‖∫ u in (0:ℝ)..1, F (s * u)‖ ≤ ∫ u in (0:ℝ)..1, ‖F (s * u)‖ :=
        intervalIntegral.norm_integral_le_integral_norm zero_le_one
      have hcs := sq_integral_le (r := fun u => ‖F (s * u)‖) hFs.norm
      rw [hD', norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg s)
      exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hcs
    have h2 : ∀ u, ‖F (s * u)‖ ^ 2 ≤ M * ∑ i, ‖Φ i (s * u) g‖ ^ 2 := by
      intro u
      have a1 : ‖F (s * u)‖ ≤ ∑ i, |y i| * ‖Φ i (s * u) g‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl (fun i _ => ?_)))
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have a2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |y i|) (fun i => ‖Φ i (s * u) g‖)
      simp only [sq_abs] at a2
      have a3 : 0 ≤ ∑ i, ‖Φ i (s * u) g‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
      calc ‖F (s * u)‖ ^ 2 ≤ (∑ i, |y i| * ‖Φ i (s * u) g‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) a1 2
        _ ≤ (∑ i, y i ^ 2) * ∑ i, ‖Φ i (s * u) g‖ ^ 2 := a2
        _ ≤ M * ∑ i, ‖Φ i (s * u) g‖ ^ 2 := mul_le_mul_of_nonneg_right hy a3
    have h3 : ∫ u in (0:ℝ)..1, ‖F (s * u)‖ ^ 2 ≤ ∫ u in (0:ℝ)..1, M * ∑ i, ‖Φ i (s * u) g‖ ^ 2 :=
      intervalIntegral.integral_mono_on zero_le_one ((hFs.norm.pow 2).intervalIntegrable 0 1)
        ((continuous_const.mul (continuous_finset_sum _ (fun i _ => ((hΦc i g).norm.pow 2)))).intervalIntegrable 0 1)
        (fun u _ => h2 u)
    have h4 : ∫ u in (0:ℝ)..1, M * ∑ i, ‖Φ i (s * u) g‖ ^ 2 =
        M * ∑ i, ∫ u in (0:ℝ)..1, ‖Φ i (s * u) g‖ ^ 2 := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_finset_sum (f := fun i u => ‖Φ i (s * u) g‖ ^ 2)
          (fun i _ => ((hΦc i g).norm.pow 2).intervalIntegrable 0 1)]
    have h5 : ∑ i, q i g = β g * ∑ i, ∫ u in (0:ℝ)..1, ‖Φ i (s * u) g‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => intervalIntegral.integral_const_mul _ _)
    rw [h5]
    have h6 : ‖D g‖ ^ 2 ≤ s ^ 2 * (M * ∑ i, ∫ u in (0:ℝ)..1, ‖Φ i (s * u) g‖ ^ 2) := by
      rw [← h4]; exact h1.trans (mul_le_mul_of_nonneg_left h3 (sq_nonneg s))
    calc β g * ‖D g‖ ^ 2 ≤ β g * (s ^ 2 * (M * ∑ i, ∫ u in (0:ℝ)..1, ‖Φ i (s * u) g‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h6 (hβ0 g)
      _ = M * s ^ 2 * (β g * ∑ i, ∫ u in (0:ℝ)..1, ‖Φ i (s * u) g‖ ^ 2) := by ring
  have hsu : ∀ u ∈ Set.Icc (0:ℝ) 1, |s * u| ≤ 1 := by
    intro u hu
    rw [abs_mul, abs_of_nonneg hu.1]
    nlinarith [abs_nonneg s, hu.2, hu.1]
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hmem : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) 1)), u ∈ Set.Icc (0:ℝ) 1 := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
    rw [Set.uIoc_of_le zero_le_one] at hu
    exact ⟨hu.1.le, hu.2⟩
  have hq : ∀ i, Integrable (q i) μ ∧ ∫ g, q i g ∂μ ≤ B i := by
    intro i
    set f : ℝ → G → ℝ := fun u g => β g * ‖Φ i (s * u) g‖ ^ 2 with hf
    have hmeas : Measurable (Function.uncurry f) := by
      have hc : Continuous fun p : ℝ × G => Φ i (s * p.1) p.2 :=
        (hΦ i).comp ((continuous_const.mul continuous_fst).prodMk continuous_snd)
      exact (hβ.comp measurable_snd).mul (hc.measurable.norm.pow_const 2)
    have hint : Integrable (Function.uncurry f)
        ((MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) 1)).prod μ) := by
      rw [integrable_prod_iff hmeas.aestronglyMeasurable]
      refine ⟨?_, ?_⟩
      · filter_upwards [hmem] with u hu
        exact (hB i (s * u) (hsu u hu)).1
      · refine (integrable_const (B i)).mono' hmeas.aestronglyMeasurable.norm.integral_prod_right' ?_
        filter_upwards [hmem] with u hu
        have e : ∫ g, ‖Function.uncurry f (u, g)‖ ∂μ = ∫ g, β g * ‖Φ i (s * u) g‖ ^ 2 ∂μ := by
          congr 1; funext g
          show ‖β g * ‖Φ i (s * u) g‖ ^ 2‖ = β g * ‖Φ i (s * u) g‖ ^ 2
          rw [Real.norm_eq_abs]
          exact abs_of_nonneg (mul_nonneg (hβ0 g) (sq_nonneg _))
        rw [e, Real.norm_eq_abs,
          abs_of_nonneg (integral_nonneg (fun g => mul_nonneg (hβ0 g) (sq_nonneg _)))]
        exact (hB i (s * u) (hsu u hu)).2
    refine ⟨?_, ?_⟩
    · have e : q i = fun g => ∫ u, f u g ∂(MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) 1)) := by
        funext g
        show ∫ u in (0:ℝ)..1, β g * ‖Φ i (s * u) g‖ ^ 2 =
          ∫ u, β g * ‖Φ i (s * u) g‖ ^ 2 ∂(MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) 1))
        rw [intervalIntegral.integral_of_le zero_le_one, Set.uIoc_of_le zero_le_one]
      rw [e]; exact hint.integral_prod_right
    · have sw := MeasureTheory.intervalIntegral_integral_swap hint
      calc ∫ g, q i g ∂μ = ∫ u in (0:ℝ)..1, ∫ g, f u g ∂μ := sw.symm
        _ ≤ ∫ u in (0:ℝ)..1, B i := by
          apply intervalIntegral.integral_mono_on zero_le_one
          · exact intervalIntegrable_iff.2 hint.integral_prod_left
          · exact intervalIntegrable_const
          · intro u hu; exact (hB i (s * u) (hsu u hu)).2
        _ = B i := by simp
  have hg_int : Integrable (fun g => M * s ^ 2 * ∑ i, q i g) μ :=
    (integrable_finset_sum _ (fun i _ => (hq i).1)).const_mul _
  calc ∫ g, β g * ‖D g‖ ^ 2 ∂μ ≤ ∫ g, M * s ^ 2 * ∑ i, q i g ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun g => mul_nonneg (hβ0 g) (sq_nonneg _)))
          hg_int (Filter.Eventually.of_forall hpt)
    _ = M * s ^ 2 * ∑ i, ∫ g, q i g ∂μ := by
        rw [integral_const_mul, integral_finset_sum _ (fun i _ => (hq i).1)]
    _ ≤ M * s ^ 2 * ∑ i, B i :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => (hq i).2)) (mul_nonneg hM (sq_nonneg s))

section Abstract

variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]

omit [TopologicalSpace G] [IsTopologicalGroup G] in

lemma decay_shift {δ : G → ℝ} (hinv : ∀ g, δ g⁻¹ = δ g) (hsub : ∀ g g', δ (g * g') ≤ δ g + δ g') {c C : ℝ}
    (hc : 0 ≤ c) {f : G → ℂ} (hf : ∀ g, ‖f g‖ ≤ C * Real.exp (-(c * δ g))) (x y g : G) :
    ‖f (x * g * y)‖ ≤ C * Real.exp (c * (δ x + δ y)) * Real.exp (-(c * δ g)) := by
  have hC : 0 ≤ C := by
    by_contra h
    have h' : C * Real.exp (-(c * δ 1)) < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge h) (Real.exp_pos _)
    linarith [norm_nonneg (f 1), hf 1]
  have hd : δ g ≤ δ x + δ (x * g * y) + δ y := by
    have e : g = x⁻¹ * (x * g * y) * y⁻¹ := by group
    have h1 := hsub (x⁻¹ * (x * g * y)) y⁻¹
    have h2 := hsub x⁻¹ (x * g * y)
    rw [← e, hinv] at h1
    rw [hinv] at h2
    linarith
  have hm := mul_le_mul_of_nonneg_left hd hc
  calc ‖f (x * g * y)‖ ≤ C * Real.exp (-(c * δ (x * g * y))) := hf _
    _ ≤ C * Real.exp (c * (δ x + δ y) + -(c * δ g)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply Real.exp_le_exp.mpr
        nlinarith
    _ = C * Real.exp (c * (δ x + δ y)) * Real.exp (-(c * δ g)) := by rw [Real.exp_add]; ring

omit [IsTopologicalGroup G] in
lemma inner_move {ρ : G → (H →L[ℂ] H)} (hρ : IsURep ρ) (x g : G) (v u : H) :
    ⟪ρ x⁻¹ v, ρ g u⟫_ℂ = ⟪v, ρ (x * g) u⟫_ℂ := by
  have hiso : ∀ h : G, ∀ a b : H, ⟪ρ h a, ρ h b⟫_ℂ = ⟪a, b⟫_ℂ := by
    intro h a b
    let L : H →ₗᵢ[ℂ] H := { toLinearMap := (ρ h : H →ₗ[ℂ] H), norm_map' := hρ.2.2.1 h }
    exact L.inner_map_map a b
  have h1 : ρ x (ρ x⁻¹ v) = v := by
    have := congrArg (fun T : H →L[ℂ] H => T v) (hρ.2.1 x x⁻¹)
    simp only [mul_inv_cancel, hρ.1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at this
    exact this.symm
  have h2 : ρ x (ρ g u) = ρ (x * g) u := by
    rw [hρ.2.1]; rfl
  rw [← hiso x (ρ x⁻¹ v) (ρ g u), h1, h2]

omit [IsTopologicalGroup G] in
lemma hasDerivAt_coef {ρ : G → (H →L[ℂ] H)} (hρ : IsURep ρ) {b : ℝ → G} (hb : ∀ s t, b (s + t) = b s * b t)
    {w u : H} (hd : HasDerivAt (fun s => ρ (b s) w) u 0) (v : H) (x : G) (t : ℝ) :
    HasDerivAt (fun s => ⟪v, ρ (x * b s) w⟫_ℂ) ⟪v, ρ (x * b t) u⟫_ℂ t := by
  set L : H →L[ℝ] ℂ := ((innerSL ℂ v).comp (ρ (x * b t))).restrictScalars ℝ with hL
  have e : ∀ s, ⟪v, ρ (x * b s) w⟫_ℂ = L (ρ (b (s - t)) w) := by
    intro s
    have hs : x * b s = (x * b t) * b (s - t) := by
      rw [mul_assoc, ← hb]; congr 2; ring
    rw [hs, hρ.2.1, hL]
    simp
  have hd' : HasDerivAt (fun s => ρ (b (s - t)) w) u t :=
    HasDerivAt.comp_sub_const t t (by rwa [sub_self])
  have key := HasFDerivAt.comp_hasDerivAt t L.hasFDerivAt hd'
  have hf : (fun s => ⟪v, ρ (x * b s) w⟫_ℂ) = L ∘ (fun s => ρ (b (s - t)) w) := by
    funext s; exact e s
  rw [hf]
  refine key.congr_deriv ?_
  rw [hL]
  simp

variable [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

lemma integrable_coef {ρ : G → (H →L[ℂ] H)} (hρ : IsURep ρ) {δ : G → ℝ} (hinv : ∀ g, δ g⁻¹ = δ g)
    (hsub : ∀ g g', δ (g * g') ≤ δ g + δ g') {c : ℝ} (hc : 0 ≤ c) {ν : Measure G}
    (hν : Integrable (fun m => Real.exp (-(c * δ m))) ν) {v u : H}
    (hu : ∃ C : ℝ, ∀ g, ‖⟪v, ρ g u⟫_ℂ‖ ≤ C * Real.exp (-(c * δ g))) (g : G) :
    Integrable (fun m => ⟪v, ρ (m * g) u⟫_ℂ) ν := by
  obtain ⟨C, hC⟩ := hu
  have hCn : 0 ≤ C := by
    by_contra h
    have h1 := hC 1
    have h2 : C * Real.exp (-(c * δ 1)) < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge h) (Real.exp_pos _)
    linarith [norm_nonneg (⟪v, ρ 1 u⟫_ℂ)]
  have hcont : Continuous fun m : G => ⟪v, ρ (m * g) u⟫_ℂ :=
    continuous_const.inner ((hρ.2.2.2 u).comp (continuous_id.mul continuous_const))
  refine Integrable.mono' (hν.const_mul (C * Real.exp (c * δ g))) hcont.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun m => ?_)
  have h2 : δ m ≤ δ (m * g) + δ g := by
    have := hsub (m * g) g⁻¹
    rwa [mul_inv_cancel_right, hinv] at this
  have hm := mul_le_mul_of_nonneg_left h2 hc
  calc ‖⟪v, ρ (m * g) u⟫_ℂ‖ ≤ C * Real.exp (-(c * δ (m * g))) := hC _
    _ ≤ C * Real.exp (c * δ g + -(c * δ m)) := by
      apply mul_le_mul_of_nonneg_left _ hCn
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = C * Real.exp (c * δ g) * Real.exp (-(c * δ m)) := by rw [Real.exp_add]; ring

lemma ftc {ρ : G → (H →L[ℂ] H)} (hρ : IsURep ρ) {δ : G → ℝ} (hδ : Continuous δ) (hinv : ∀ g, δ g⁻¹ = δ g)
    (hsub : ∀ g g', δ (g * g') ≤ δ g + δ g') {c : ℝ} (hc : 0 ≤ c) {ν : Measure G} [SFinite ν]
    (hν : Integrable (fun m => Real.exp (-(c * δ m))) ν) {b : ℝ → G} (hbc : Continuous b) (hb0 : b 0 = 1)
    (hb : ∀ s t, b (s + t) = b s * b t) {v w u : H} (hd : HasDerivAt (fun s => ρ (b s) w) u 0)
    (hw : ∃ C : ℝ, ∀ g, ‖⟪v, ρ g w⟫_ℂ‖ ≤ C * Real.exp (-(c * δ g)))
    (hu : ∃ C : ℝ, ∀ g, ‖⟪v, ρ g u⟫_ℂ‖ ≤ C * Real.exp (-(c * δ g))) (g : G) (s : ℝ) :
    (∫ m, ⟪v, ρ (m * (g * b s)) w⟫_ℂ ∂ν) - ∫ m, ⟪v, ρ (m * g) w⟫_ℂ ∂ν =
      ∫ t in (0:ℝ)..s, ∫ m, ⟪v, ρ (m * (g * b t)) u⟫_ℂ ∂ν := by
  have hcontF' : Continuous fun p : G × ℝ => ⟪v, ρ (p.1 * (g * b p.2)) u⟫_ℂ :=
    continuous_const.inner ((hρ.2.2.2 u).comp
      (continuous_fst.mul (continuous_const.mul (hbc.comp continuous_snd))))
  have hpt : ∀ m : G, ⟪v, ρ (m * (g * b s)) w⟫_ℂ - ⟪v, ρ (m * g) w⟫_ℂ =
      ∫ t in (0:ℝ)..s, ⟪v, ρ (m * (g * b t)) u⟫_ℂ := by
    intro m
    have hder : ∀ t ∈ Set.uIcc (0:ℝ) s, HasDerivAt (fun r => ⟪v, ρ (m * (g * b r)) w⟫_ℂ)
        ⟪v, ρ (m * (g * b t)) u⟫_ℂ t := by
      intro t _
      have := hasDerivAt_coef hρ hb hd v (m * g) t
      simpa only [mul_assoc] using this
    have hint : IntervalIntegrable (fun t => ⟪v, ρ (m * (g * b t)) u⟫_ℂ) MeasureTheory.volume 0 s :=
      (hcontF'.comp (Continuous.prodMk continuous_const continuous_id)).intervalIntegrable 0 s
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint, hb0, mul_one]
  obtain ⟨K, hK⟩ := (isCompact_uIcc (a := (0:ℝ)) (b := s)).exists_bound_of_continuousOn
    ((hδ.comp hbc).continuousOn)
  obtain ⟨C, hC⟩ := hu
  have hCn : 0 ≤ C := by
    by_contra h
    have h1 := hC 1
    have h2 : C * Real.exp (-(c * δ 1)) < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge h) (Real.exp_pos _)
    linarith [norm_nonneg (⟪v, ρ 1 u⟫_ℂ)]
  have hbd : ∀ t ∈ Set.uIcc (0:ℝ) s, ∀ m, ‖⟪v, ρ (m * (g * b t)) u⟫_ℂ‖ ≤
      C * Real.exp (c * (δ g + K)) * Real.exp (-(c * δ m)) := by
    intro t ht m
    have h1 : δ m ≤ δ (m * (g * b t)) + δ g + δ (b t) := by
      have a1 := hsub (m * (g * b t)) (g * b t)⁻¹
      have a2 := hsub g (b t)
      rw [mul_inv_cancel_right, hinv] at a1
      linarith
    have h2 : δ (b t) ≤ K := le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hK t ht)
    have h3 := mul_le_mul_of_nonneg_left h1 hc
    have h4 := mul_le_mul_of_nonneg_left h2 hc
    calc ‖⟪v, ρ (m * (g * b t)) u⟫_ℂ‖ ≤ C * Real.exp (-(c * δ (m * (g * b t)))) := hC _
      _ ≤ C * Real.exp (c * (δ g + K) + -(c * δ m)) := by
        apply mul_le_mul_of_nonneg_left _ hCn
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = C * Real.exp (c * (δ g + K)) * Real.exp (-(c * δ m)) := by rw [Real.exp_add]; ring
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) s)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hprod : Integrable (Function.uncurry fun t m => ⟪v, ρ (m * (g * b t)) u⟫_ℂ)
      ((MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) s)).prod ν) := by
    have hmaj : Integrable (fun p : ℝ × G => (1:ℝ) * (C * Real.exp (c * (δ g + K)) * Real.exp (-(c * δ p.2))))
        ((MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) s)).prod ν) :=
      (integrable_const (1:ℝ)).mul_prod (hν.const_mul _)
    refine hmaj.mono' (hcontF'.comp continuous_swap).aestronglyMeasurable ?_
    filter_upwards [(Measure.quasiMeasurePreserving_fst).ae (ae_restrict_mem measurableSet_uIoc)] with p hp
    have := hbd p.1 (Set.uIoc_subset_uIcc hp) p.2
    rw [one_mul]; exact this
  have hi1 : Integrable (fun m => ⟪v, ρ (m * (g * b s)) w⟫_ℂ) ν :=
    integrable_coef hρ hinv hsub hc hν hw (g * b s)
  have hi0 : Integrable (fun m => ⟪v, ρ (m * g) w⟫_ℂ) ν := integrable_coef hρ hinv hsub hc hν hw g
  rw [← integral_sub hi1 hi0]
  simp_rw [hpt]
  exact (MeasureTheory.intervalIntegral_integral_swap hprod).symm

lemma integral_conj {ν : Measure G} {x : G} {r : ℝ} (hr : 0 ≤ r)
    (h : ν.map (fun m => x * m * x⁻¹) = ENNReal.ofReal r • ν) (f : G → ℂ) :
    ∫ m, f (x * m * x⁻¹) ∂ν = (r : ℂ) * ∫ m, f m ∂ν := by
  let e : G ≃ₜ G := (Homeomorph.mulLeft x).trans (Homeomorph.mulRight x⁻¹)
  have he : (e.toMeasurableEquiv : G → G) = fun m => x * m * x⁻¹ := rfl
  have key := integral_map_equiv e.toMeasurableEquiv f (μ := ν)
  simp only [he] at key
  rw [h, integral_smul_measure, ENNReal.toReal_ofReal hr] at key
  rw [← key, Complex.real_smul]

lemma integral_right {ν : Measure G} {x : G} (h : ν.map (fun m => m * x) = ν) (f : G → ℂ) :
    ∫ m, f (m * x) ∂ν = ∫ m, f m ∂ν := by
  have he : ((Homeomorph.mulRight x).toMeasurableEquiv : G → G) = fun m => m * x := rfl
  have key := integral_map_equiv (Homeomorph.mulRight x).toMeasurableEquiv f (μ := ν)
  simp only [he] at key
  rw [h] at key
  exact key.symm

end Abstract

variable {n : ℕ} {ε : Fin n → Bool}

lemma isURep_umat {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) :
    IsURep fun g : UJ ε => σ (umat g) := by
  have hm : ∀ g : UJ ε, umat g ∈ UJset ε := fun g => g.2
  refine ⟨hσ.1.1, fun a b => hσ.1.2 _ (hm a) _ (hm b), fun g v => hσ.2.1 _ (hm g) v, fun v => ?_⟩
  exact (hσ.2.2 v).comp_continuous (Units.continuous_val.comp continuous_subtype_val) hm

lemma onePar {a : ℝ → UJ ε} {X : Matrix (Fin n) (Fin n) ℂ}
    (ha : ∀ s : ℝ, umat (a s) = NormedSpace.exp ((s : ℂ) • X)) :
    Continuous a ∧ a 0 = 1 ∧ (∀ s t, a (s + t) = a s * a t) ∧ ∀ s, (a s)⁻¹ = a (-s) := by
  have hexp : ∀ s t : ℝ, NormedSpace.exp (((s + t : ℝ) : ℂ) • X) =
      NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((t : ℂ) • X) := by
    intro s t
    rw [Complex.ofReal_add, add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)
  have hadd : ∀ s t, a (s + t) = a s * a t := fun s t => Subtype.ext (Units.ext (by
    change umat (a (s + t)) = umat (a s) * umat (a t)
    rw [ha, ha, ha, hexp]))
  have h0 : a 0 = 1 := Subtype.ext (Units.ext (by
    change umat (a 0) = 1
    rw [ha]; simp))
  have hinv : ∀ s, (a s)⁻¹ = a (-s) := fun s =>
    inv_eq_of_mul_eq_one_right (by rw [← hadd, add_neg_cancel, h0])
  have hsm : Continuous fun s : ℝ => (s : ℂ) • X := Complex.continuous_ofReal.smul continuous_const
  have hc : Continuous fun s : ℝ => NormedSpace.exp ((s : ℂ) • X) := by
    letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
    letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
    haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
    exact NormedSpace.exp_continuous.comp hsm
  refine ⟨?_, h0, hadd, hinv⟩
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · exact hc.congr (fun s => (ha s).symm)
  · refine (hc.comp continuous_neg).congr (fun s => ?_)
    show NormedSpace.exp (((-s : ℝ) : ℂ) • X) = umat (a s)⁻¹
    rw [hinv, ha]

lemma conj_facts {k : UJ ε} (hk : umat k ∈ Kset ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    inG ε (umat k⁻¹ * X * umat k) ∧
      ((umat k⁻¹ * X * umat k) * (umat k⁻¹ * X * umat k)ᴴ).trace = (X * Xᴴ).trace ∧
      ∀ s : ℝ, NormedSpace.exp ((s : ℂ) • (umat k⁻¹ * X * umat k)) =
        umat k⁻¹ * NormedSpace.exp ((s : ℂ) • X) * umat k := by
  obtain ⟨hku, hkJ⟩ := hk
  have hinvk : umat k⁻¹ = star (umat k) := by
    have h1 : umat k⁻¹ * umat k = 1 := by
      change (((k⁻¹ : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * _ = 1
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
    have h2 : star (umat k) * umat k = 1 := Matrix.mem_unitaryGroup_iff'.1 hku
    calc umat k⁻¹ = umat k⁻¹ * (umat k * star (umat k)) := by
            rw [Matrix.mem_unitaryGroup_iff.1 hku, mul_one]
      _ = star (umat k) := by rw [← mul_assoc, h1, one_mul]
  have hJk : Jm ε * star (umat k) = star (umat k) * Jm ε := by
    have := congrArg star hkJ
    simp only [star_mul, Matrix.star_eq_conjTranspose, Jm_conjTranspose] at this
    simpa [Matrix.star_eq_conjTranspose] using this
  have hJ : (Jm ε)ᴴ = Jm ε := Jm_conjTranspose ε
  set K := umat k
  rw [hinvk]
  refine ⟨?_, ?_, ?_⟩
  · unfold inG at hX ⊢
    simp only [Matrix.star_eq_conjTranspose] at hJk ⊢
    calc (Kᴴ * X * K)ᴴ * Jm ε + Jm ε * (Kᴴ * X * K)
        = Kᴴ * (Xᴴ * Jm ε + Jm ε * X) * K := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_add,
            Matrix.add_mul, Matrix.mul_assoc]
          rw [hkJ, ← Matrix.mul_assoc (Jm ε) Kᴴ, hJk, Matrix.mul_assoc]
      _ = 0 := by rw [hX]; simp
  · simp only [Matrix.star_eq_conjTranspose]
    have hu : K * Kᴴ = 1 := by simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.1 hku
    have : Kᴴ * X * K * (Kᴴ * X * K)ᴴ = Kᴴ * (X * Xᴴ) * K := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc K Kᴴ, hu, Matrix.one_mul]
    rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hu, Matrix.one_mul]
  · intro s
    have hu : K * star K = 1 := Matrix.mem_unitaryGroup_iff.1 hku
    have hu' : star K * K = 1 := Matrix.mem_unitaryGroup_iff'.1 hku
    let U : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨star K, K, hu', hu⟩
    have key := Matrix.exp_units_conj U ((s : ℂ) • X)
    have e1 : ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = K := rfl
    rw [e1] at key
    change NormedSpace.exp (star K * ((s : ℂ) • X) * K) = star K * NormedSpace.exp ((s : ℂ) • X) * K at key
    rw [← key, Matrix.mul_smul, Matrix.smul_mul]

lemma norm_shift (hn : 1 ≤ n) {W : Submodule ℂ (Fin n → ℂ)} {ν : Measure (UJ ε)} (hW : IsIsoC ε W)
    (hν : IsHaarSub (NW ε W) ν) {β : UJ ε → ENNReal} (hβ : Measurable β) (hβt : ∀ y, β y ≠ ⊤)
    (hβ1 : ∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1) {x : UJ ε} {r : ℝ}
    (h1 : ν.map (fun m => x * m * x⁻¹) = ENNReal.ofReal (Real.exp r) • ν)
    (h2 : ν.map (fun m => x⁻¹ * m * x⁻¹⁻¹) = ENNReal.ofReal (Real.exp (-r)) • ν)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d c : ℝ} (hσ : IsURepOn (UJset ε) σ)
    (hd : IsFdeg (muG ε) σ d) (hc : 8 * n * rkR ε < c) {v u : H}
    (hu : ∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) u⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g))))
    (hv : ∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) v⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) :
    Integrable (fun g : UJ ε => (β g).toReal * ‖∫ m, ⟪v, σ (umat (m * (x * g))) u⟫_ℂ ∂ν‖ ^ 2) (muG ε) ∧
      ∫ g : UJ ε, (β g).toReal * ‖∫ m, ⟪v, σ (umat (m * (x * g))) u⟫_ℂ ∂ν‖ ^ 2 ∂(muG ε) =
        Real.exp (-r) * ((∫ m, ⟪v, σ (umat m) v⟫_ℂ ∂ν).re * (‖u‖ ^ 2 / d)) := by
  have hρ : IsURep (fun g : UJ ε => σ (umat g)) := isURep_umat hσ
  have im : ∀ (a g' : UJ ε) (p q : H), ⟪σ (umat a⁻¹) p, σ (umat g') q⟫_ℂ = ⟪p, σ (umat (a * g')) q⟫_ℂ :=
    fun a g' p q => inner_move hρ a g' p q
  have hmul : ∀ a b : UJ ε, σ (umat (a * b)) = (σ (umat a)).comp (σ (umat b)) := fun a b => hρ.2.1 a b
  have cd := GlobalTheory.Count.Cartan.cartan_distances n ε
  have hinv : ∀ g : UJ ε, dOp (umat g⁻¹) = dOp (umat g) := fun g => (cd.2.1 g g hn).2.1
  have hsub : ∀ g g' : UJ ε, dOp (umat (g * g')) ≤ dOp (umat g) + dOp (umat g') :=
    fun g g' => (cd.2.1 g g' hn).2.2.1
  have hc0 : 0 ≤ c := le_trans (by positivity) hc.le
  set v₁ := σ (umat x⁻¹) v with hv₁
  have hA : ∀ g, ∫ m, ⟪v, σ (umat (m * (x * g))) u⟫_ℂ ∂ν =
      (Real.exp (-r) : ℂ) * ∫ m, ⟪v₁, σ (umat (m * g)) u⟫_ℂ ∂ν := by
    intro g
    have key := integral_conj (Real.exp_pos r).le h1 (fun m => ⟪v, σ (umat (m * (x * g))) u⟫_ℂ)
    have e : ∀ m, ⟪v, σ (umat (x * m * x⁻¹ * (x * g))) u⟫_ℂ = ⟪v₁, σ (umat (m * g)) u⟫_ℂ := by
      intro m
      have : x * m * x⁻¹ * (x * g) = x * (m * g) := by group
      rw [this, hv₁, im]
    simp only [e] at key
    rw [key, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      Complex.ofReal_one, one_mul]
  obtain ⟨Cu, hCu⟩ := hu
  obtain ⟨Cv, hCv⟩ := hv
  have hd1 : ∃ C : ℝ, ∀ g : UJ ε, ‖⟪v₁, σ (umat g) u⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g))) := by
    refine ⟨Cu * Real.exp (c * (dOp (umat x) + dOp (umat (1 : UJ ε)))), fun g => ?_⟩
    have := decay_shift (δ := fun g : UJ ε => dOp (umat g)) hinv hsub hc0
      (f := fun g : UJ ε => ⟪v, σ (umat g) u⟫_ℂ) hCu x 1 g
    rw [hv₁, im]
    simpa only [mul_one] using this
  have hd2 : ∃ C : ℝ, ∀ g : UJ ε, ‖⟪v₁, σ (umat g) v₁⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g))) := by
    refine ⟨Cv * Real.exp (c * (dOp (umat x) + dOp (umat x⁻¹))), fun g => ?_⟩
    have := decay_shift (δ := fun g : UJ ε => dOp (umat g)) hinv hsub hc0
      (f := fun g : UJ ε => ⟪v, σ (umat g) v⟫_ℂ) hCv x x⁻¹ g
    have e : ⟪v₁, σ (umat g) v₁⟫_ℂ = ⟪v, σ (umat (x * g * x⁻¹)) v⟫_ℂ := by
      rw [hv₁, im, hmul (x * g) x⁻¹]; rfl
    rw [e]; exact this
  obtain ⟨-, hI2, hI3⟩ := GlobalTheory.T.unitary_rep_matrix_coefficient_bound n ε W ν hW hν β hβ hβt hβ1 H σ d c u v₁ v₁ hσ hd hc hd1 hd1 hd2
  have hpt : ∀ g, ((β g).toReal : ℂ) * ((∫ m, ⟪v₁, σ (umat (m * g)) u⟫_ℂ ∂ν) *
      star (∫ m, ⟪v₁, σ (umat (m * g)) u⟫_ℂ ∂ν)) =
      (((β g).toReal * ‖∫ m, ⟪v₁, σ (umat (m * g)) u⟫_ℂ ∂ν‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  simp_rw [hpt] at hI2 hI3
  have hR : Integrable (fun g => (β g).toReal * ‖∫ m, ⟪v₁, σ (umat (m * g)) u⟫_ℂ ∂ν‖ ^ 2) (muG ε) := by
    exact hI2.re.congr (Filter.Eventually.of_forall (fun g => by
      simp only [RCLike.re_to_complex, Complex.ofReal_re]))
  rw [integral_complex_ofReal] at hI3
  have hR3 : ∫ g, (β g).toReal * ‖∫ m, ⟪v₁, σ (umat (m * g)) u⟫_ℂ ∂ν‖ ^ 2 ∂(muG ε) =
      ((∫ m, ⟪v₁, σ (umat m) v₁⟫_ℂ ∂ν) * ((‖u‖ ^ 2 / d : ℝ) : ℂ)).re := by
    rw [← hI3, Complex.ofReal_re]
  have hvv : ∫ m, ⟪v₁, σ (umat m) v₁⟫_ℂ ∂ν = (Real.exp r : ℂ) * ∫ m, ⟪v, σ (umat m) v⟫_ℂ ∂ν := by
    have key := integral_conj (Real.exp_pos r).le h1 (fun m => ⟪v, σ (umat m) v⟫_ℂ)
    rw [← key]
    congr 1; funext m
    rw [hv₁, im, hmul (x * m) x⁻¹]; rfl
  have hfun : (fun g => (β g).toReal * ‖∫ m, ⟪v, σ (umat (m * (x * g))) u⟫_ℂ ∂ν‖ ^ 2) =
      fun g => Real.exp (-r) ^ 2 * ((β g).toReal * ‖∫ m, ⟪v₁, σ (umat (m * g)) u⟫_ℂ ∂ν‖ ^ 2) := by
    funext g
    rw [hA g, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; ring
  rw [hfun]
  refine ⟨hR.const_mul _, ?_⟩
  rw [integral_const_mul, hR3, hvv]
  have he : Real.exp (-r) * Real.exp r = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_zero]
  calc _ = Real.exp (-r) * (Real.exp (-r) * Real.exp r) *
        ((∫ m, ⟪v, σ (umat m) v⟫_ℂ ∂ν).re * (‖u‖ ^ 2 / d)) := by ring
    _ = _ := by rw [he, mul_one]

theorem torus_lipschitz : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)), IsIsoC ε W → IsHaarSub (NW ε W) ν → ∀ β : UJ ε → ENNReal, Measurable β → (∀ y, β y ≠ ⊤) → (∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1) → ∀ (a : ℝ → UJ ε) (Hm : Matrix (Fin n) (Fin n) ℂ), inP ε Hm → (∀ s : ℝ, umat (a s) = NormedSpace.exp ((s : ℂ) • Hm)) → (∀ g : UJ ε, ∃ k : UJ ε, umat k ∈ Kset ε ∧ ∀ s, a s * g * (k⁻¹ * a s * k)⁻¹ * g⁻¹ ∈ NW ε W) → ∀ κ : ℝ, (∀ s, ν.map (fun m => a s * m * (a s)⁻¹) = ENNReal.ofReal (Real.exp (κ * s)) • ν) → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d c : ℝ) (w : H) (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] H), IsURepOn (UJset ε) σ → IsFdeg (muG ε) σ d → 8 * n * rkR ε < c → (∀ X, inG ε X → HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) w) (L X) 0) → ∃ C₀ : ℝ, ∀ v : H, (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) w⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) v⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → (∀ X, inG ε X → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) (L X)⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g))))) → ∀ s : ℝ, |s| ≤ 1 → ∫ g : UJ ε, (β g).toReal * ‖(∫ m, ⟪v, σ (umat (m * (a s * g))) w⟫_ℂ ∂ν) - (∫ m, ⟪v, σ (umat (m * g)) w⟫_ℂ ∂ν)‖ ^ 2 ∂(muG ε) ≤ C₀ * s ^ 2 * (∫ m, ⟪v, σ (umat m) v⟫_ℂ ∂ν).re := by
  intro n ε W ν hW hν β hβ hβt hβ1 a Hm hHm ha hconj κ hκ H _ _ _ σ d c w L hσ hd hc hL
  obtain ⟨E, hE1, -, hE3⟩ := GlobalTheory.LieONB.exists_orthonormal_basis n ε
  refine ⟨((Hm * Hmᴴ).trace).re * Real.exp |κ| * ∑ i, ‖L (E i)‖ ^ 2 / d, ?_⟩
  intro v hvw hvv hvL s hs
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have e : ∀ g : UJ ε, (∫ m, ⟪v, σ (umat (m * (a s * g))) w⟫_ℂ ∂ν) -
        (∫ m, ⟪v, σ (umat (m * g)) w⟫_ℂ ∂ν) = 0 := by
      intro g; rw [sub_eq_zero]; congr 1
    have hz : ∑ i : Fin (0 ^ 2), ‖L (E i)‖ ^ 2 / d = 0 :=
      Finset.sum_eq_zero (fun i _ => absurd i.2 (by simp))
    rw [hz]
    simp [e]
  have hn : 1 ≤ n := hnpos
  have hρ : IsURep (fun g : UJ ε => σ (umat g)) := isURep_umat hσ
  have cd := GlobalTheory.Count.Cartan.cartan_distances n ε
  have hinv : ∀ g : UJ ε, dOp (umat g⁻¹) = dOp (umat g) := fun g => (cd.2.1 g g hn).2.1
  have hsub : ∀ g g' : UJ ε, dOp (umat (g * g')) ≤ dOp (umat g) + dOp (umat g') :=
    fun g g' => (cd.2.1 g g' hn).2.2.1
  have hδc : Continuous fun g : UJ ε => dOp (umat g) := cd.2.2.2.2
  have hnr : (0:ℝ) ≤ (n:ℝ) * (rkR ε : ℝ) := mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg _)
  have hc0 : 0 ≤ c := by nlinarith
  have hνint : Integrable (fun m : UJ ε => Real.exp (-(c * dOp (umat m)))) ν :=
    (GlobalTheory.T.unipotentRadical_volume_growth n ε W ν hW hν).2 c (by nlinarith)
  haveI : SigmaFinite ν := by
    obtain ⟨C, hC⟩ := (GlobalTheory.T.unipotentRadical_volume_growth n ε W ν hW hν).1
    exact ({ set := fun k : ℕ => {m : UJ ε | dOp (umat m) ≤ k}
             set_mem := fun _ => Set.mem_univ _
             finite := fun k => (hC k (Nat.cast_nonneg k)).trans_lt ENNReal.ofReal_lt_top
             spanning := Set.eq_univ_of_forall fun m =>
               Set.mem_iUnion.2 ⟨⌈dOp (umat m)⌉₊, show dOp (umat m) ≤ (⌈dOp (umat m)⌉₊ : ℝ) from Nat.le_ceil _⟩ } :
             ν.FiniteSpanningSetsIn Set.univ).sigmaFinite
  have hNW := GlobalTheory.T.haar_subgroup_bi_invariant n ε W ν hW hν
  obtain ⟨haC, -, -, hainv⟩ := onePar ha
  have hnorm : ∀ X, inG ε X → ((X * Xᴴ).trace).re = ∑ i, (((X * (E i)ᴴ).trace).re) ^ 2 := by
    intro X hX
    have hXe := hE3 X hX
    have h1 : X * Xᴴ = ∑ i, ((((X * (E i)ᴴ).trace).re : ℝ) : ℂ) • (E i * Xᴴ) := by
      calc X * Xᴴ = (∑ i, ((((X * (E i)ᴴ).trace).re : ℝ) : ℂ) • E i) * Xᴴ := by rw [← hXe]
        _ = _ := by rw [Finset.sum_mul]; simp_rw [Matrix.smul_mul]
    have h2 : ∀ i, ((E i * Xᴴ).trace).re = ((X * (E i)ᴴ).trace).re := by
      intro i
      have : E i * Xᴴ = (X * (E i)ᴴ)ᴴ := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      rw [this, Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re]
    rw [h1, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, h2, sq]
  have hM : 0 ≤ ((Hm * Hmᴴ).trace).re := by
    rw [hnorm Hm hHm.1]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hΦ : ∀ i, Continuous fun p : ℝ × UJ ε =>
      ∫ m, ⟪v, σ (umat (m * (a p.1 * p.2))) (L (E i))⟫_ℂ ∂ν := by
    intro i
    have hu := hvL (E i) (hE1 i).1
    have hc' := (GlobalTheory.T.unitary_rep_matrix_coefficient_bound n ε W ν hW hν β hβ hβt hβ1 H σ d c (L (E i)) v v hσ hd hc hu hu hvv).1
    exact hc'.comp ((haC.comp continuous_fst).mul continuous_snd)
  have hB : ∀ i (t : ℝ), |t| ≤ 1 →
      Integrable (fun g => (β g).toReal * ‖∫ m, ⟪v, σ (umat (m * (a t * g))) (L (E i))⟫_ℂ ∂ν‖ ^ 2) (muG ε) ∧
      ∫ g, (β g).toReal * ‖∫ m, ⟪v, σ (umat (m * (a t * g))) (L (E i))⟫_ℂ ∂ν‖ ^ 2 ∂(muG ε) ≤
        Real.exp |κ| * ((∫ m, ⟪v, σ (umat m) v⟫_ℂ ∂ν).re * (‖L (E i)‖ ^ 2 / d)) := by
    intro i t ht
    have h2 : ν.map (fun m => (a t)⁻¹ * m * (a t)⁻¹⁻¹) = ENNReal.ofReal (Real.exp (-(κ * t))) • ν := by
      have := hκ (-t); rw [← hainv t, mul_neg] at this; exact this
    obtain ⟨hI, hE⟩ := norm_shift hn hW hν hβ hβt hβ1 (hκ t) h2 hσ hd hc (hvL (E i) (hE1 i).1) hvv
    refine ⟨hI, ?_⟩
    have h0 : 0 ≤ ∫ g, (β g).toReal * ‖∫ m, ⟪v, σ (umat (m * (a t * g))) (L (E i))⟫_ℂ ∂ν‖ ^ 2 ∂(muG ε) :=
      integral_nonneg (fun g => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
    rw [hE] at h0 ⊢
    have hexp : Real.exp (-(κ * t)) ≤ Real.exp |κ| := by
      apply Real.exp_le_exp.mpr
      have : |κ * t| ≤ |κ| := by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg κ) ht
      linarith [neg_le_abs (κ * t)]
    exact mul_le_mul_of_nonneg_right hexp ((mul_nonneg_iff_of_pos_left (Real.exp_pos _)).1 h0)
  have hD : ∀ g : UJ ε, ∃ y : Fin (n ^ 2) → ℝ, ∑ i, y i ^ 2 ≤ ((Hm * Hmᴴ).trace).re ∧
      (∫ m, ⟪v, σ (umat (m * (a s * g))) w⟫_ℂ ∂ν) - (∫ m, ⟪v, σ (umat (m * g)) w⟫_ℂ ∂ν) =
        ∫ t in (0:ℝ)..s, ∑ i, (y i : ℂ) * ∫ m, ⟪v, σ (umat (m * (a t * g))) (L (E i))⟫_ℂ ∂ν := by
    intro g
    obtain ⟨k, hk, hkn⟩ := hconj g
    obtain ⟨hXg, htr, hexpg⟩ := conj_facts hk hHm.1
    set Xg := umat k⁻¹ * Hm * umat k with hXgdef
    refine ⟨fun i => ((Xg * (E i)ᴴ).trace).re, ?_, ?_⟩
    · show ∑ i, (((Xg * (E i)ᴴ).trace).re) ^ 2 ≤ ((Hm * Hmᴴ).trace).re
      rw [← hnorm Xg hXg, htr]
    obtain ⟨b, hbdef⟩ : ∃ b : ℝ → UJ ε, b = fun t => k⁻¹ * a t * k := ⟨_, rfl⟩
    have hbX : ∀ t : ℝ, umat (b t) = NormedSpace.exp ((t : ℂ) • Xg) := by
      intro t
      rw [hexpg t, hbdef]
      show umat k⁻¹ * umat (a t) * umat k = _
      rw [ha t]
    obtain ⟨hbc, hb0, hbh, -⟩ := onePar hbX
    have hder : HasDerivAt (fun t : ℝ => σ (umat (b t)) w) (L Xg) 0 := by
      have e : (fun t : ℝ => σ (umat (b t)) w) = fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • Xg)) w := by
        funext t; rw [hbX]
      rw [e]; exact hL Xg hXg
    have hF : (∫ m, ⟪v, σ (umat (m * (g * b s))) w⟫_ℂ ∂ν) - ∫ m, ⟪v, σ (umat (m * g)) w⟫_ℂ ∂ν =
        ∫ t in (0:ℝ)..s, ∫ m, ⟪v, σ (umat (m * (g * b t))) (L Xg)⟫_ℂ ∂ν :=
      ftc (ρ := fun g : UJ ε => σ (umat g)) (δ := fun g : UJ ε => dOp (umat g)) hρ hδc hinv hsub hc0
        hνint hbc hb0 hbh hder hvw (hvL Xg hXg) g s
    have hinvar : ∀ (t : ℝ) (u : H), ∫ m, ⟪v, σ (umat (m * (g * b t))) u⟫_ℂ ∂ν =
        ∫ m, ⟪v, σ (umat (m * (a t * g))) u⟫_ℂ ∂ν := by
      intro t u
      have hn' : a t * g * (b t)⁻¹ * g⁻¹ ∈ NW ε W := by rw [hbdef]; exact hkn t
      have key := integral_right (hNW.1 _ hn') (fun m => ⟪v, σ (umat (m * (g * b t))) u⟫_ℂ)
      rw [← key]
      congr 1; funext m
      have e : m * (a t * g * (b t)⁻¹ * g⁻¹) * (g * b t) = m * (a t * g) := by group
      simp only [e]
    have hint_i : ∀ (t : ℝ) i, Integrable (fun m => ⟪v, σ (umat (m * (a t * g))) (L (E i))⟫_ℂ) ν :=
      fun t i => integrable_coef (ρ := fun g : UJ ε => σ (umat g)) (δ := fun g : UJ ε => dOp (umat g))
        hρ hinv hsub hc0 hνint (hvL (E i) (hE1 i).1) (a t * g)
    have hLX : L Xg = ∑ i, (((Xg * (E i)ᴴ).trace).re) • L (E i) := by
      conv_lhs => rw [hE3 Xg hXg]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← map_smul]; congr 1
    have hDform : ∀ t : ℝ, ∫ m, ⟪v, σ (umat (m * (a t * g))) (L Xg)⟫_ℂ ∂ν =
        ∑ i, ((((Xg * (E i)ᴴ).trace).re : ℝ) : ℂ) *
          ∫ m, ⟪v, σ (umat (m * (a t * g))) (L (E i))⟫_ℂ ∂ν := by
      intro t
      rw [hLX]
      have hpt : ∀ m : UJ ε, ⟪v, σ (umat (m * (a t * g))) (∑ i, (((Xg * (E i)ᴴ).trace).re) • L (E i))⟫_ℂ =
          ∑ i, ((((Xg * (E i)ᴴ).trace).re : ℝ) : ℂ) * ⟪v, σ (umat (m * (a t * g))) (L (E i))⟫_ℂ := by
        intro m
        rw [map_sum, inner_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [ContinuousLinearMap.map_smul_of_tower, ← Complex.coe_smul, inner_smul_right]
      simp only [hpt]
      rw [integral_finset_sum _ (fun i _ => (hint_i t i).const_mul _)]
      simp_rw [integral_const_mul]
    show (∫ m, ⟪v, σ (umat (m * (a s * g))) w⟫_ℂ ∂ν) - (∫ m, ⟪v, σ (umat (m * g)) w⟫_ℂ ∂ν) =
      ∫ t in (0:ℝ)..s, ∑ i, ((((Xg * (E i)ᴴ).trace).re : ℝ) : ℂ) *
        ∫ m, ⟪v, σ (umat (m * (a t * g))) (L (E i))⟫_ℂ ∂ν
    rw [← hinvar s w, hF]
    congr 1; funext t
    rw [hinvar t, hDform t]
  have key := torus_lipschitz_l2_bound (muG ε) (fun g => (β g).toReal) hβ.ennreal_toReal (fun g => ENNReal.toReal_nonneg)
    (fun i t g => ∫ m, ⟪v, σ (umat (m * (a t * g))) (L (E i))⟫_ℂ ∂ν) hΦ
    (fun g => (∫ m, ⟪v, σ (umat (m * (a s * g))) w⟫_ℂ ∂ν) - ∫ m, ⟪v, σ (umat (m * g)) w⟫_ℂ ∂ν)
    ((Hm * Hmᴴ).trace).re s hM hs
    (fun i => Real.exp |κ| * ((∫ m, ⟪v, σ (umat m) v⟫_ℂ ∂ν).re * (‖L (E i)‖ ^ 2 / d))) hD hB
  refine key.trans (le_of_eq ?_)
  have hs' : ∑ i, Real.exp |κ| * ((∫ m, ⟪v, σ (umat m) v⟫_ℂ ∂ν).re * (‖L (E i)‖ ^ 2 / d)) =
      Real.exp |κ| * (∫ m, ⟪v, σ (umat m) v⟫_ℂ ∂ν).re * ∑ i, ‖L (E i)‖ ^ 2 / d := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hs']; ring

end GlobalTheory.TorusLip
