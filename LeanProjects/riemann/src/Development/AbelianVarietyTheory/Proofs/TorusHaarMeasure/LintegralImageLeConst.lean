import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH

namespace GlobalTheory.FrameLoc

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
  MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

noncomputable section

theorem lintegral_image_le_const {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]
    {Θ : F → F} (hΘ : ContDiff ℝ 1 Θ) {A : Set F} (hA : MeasurableSet A) {M : ℝ}
    (hM : A ⊆ Metric.closedBall 0 M) (hinj : Set.InjOn Θ A) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ G : F → ℝ≥0∞, ∫⁻ x in Θ '' A, G x ∂μ ≤ K * ∫⁻ y in A, G (Θ y) ∂μ := by
  have hc : Continuous fun y => |(fderiv ℝ Θ y).det| :=
    (ContinuousLinearMap.continuous_det.comp (hΘ.continuous_fderiv (by simp))).abs
  haveI : ProperSpace F := FiniteDimensional.proper ℝ F
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : F) M).bddAbove_image hc.continuousOn
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_lt_top, fun G => ?_⟩
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hA (f' := fderiv ℝ Θ)
    (fun x _ => ((hΘ.differentiable (by simp)) x).hasFDerivAt.hasFDerivWithinAt) hinj,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' hA fun y hy => ?_
  gcongr
  exact hC ⟨y, hM hy, rfl⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def lowPart (y : Frame X.Ψ r) : V (nd X) :=
  WithLp.toLp 2 fun j => y ((Fintype.equivFin (Ent X)).symm j).1
    ((Fintype.equivFin (Ent X)).symm j).2.1.1 ((Fintype.equivFin (Ent X)).symm j).2.1.2

def upPart (y : Frame X.Ψ r) : Frame X.Ψ r := fun τ a c => if c < a then 0 else y τ a c

def glue (z : V (nd X)) (b : Frame X.Ψ r) : Frame X.Ψ r := fun τ a c =>
  if h : c < a then z ((Fintype.equivFin (Ent X)) ⟨τ, ⟨(a, c), h⟩⟩) else b τ a c

theorem lowPart_apply (y : Frame X.Ψ r) (τ : X.Ψ) (a c : Fin r) (h : c < a) :
    lowPart X y ((Fintype.equivFin (Ent X)) ⟨τ, ⟨(a, c), h⟩⟩) = y τ a c := by
  simp [lowPart]

theorem lowPart_glue (z : V (nd X)) (b : Frame X.Ψ r) : lowPart X (glue X z b) = z := by
  ext j
  obtain ⟨⟨τ, ⟨⟨a, c⟩, h⟩⟩, rfl⟩ := (Fintype.equivFin (Ent X)).surjective j
  rw [lowPart_apply X _ τ a c h]
  simp only [glue]
  rw [dif_pos h]

theorem upPart_glue (z : V (nd X)) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    upPart X (glue X z b) = b := by
  funext τ a c
  by_cases h : c < a
  · simp [upPart, h, (hb τ).2 a c h]
  · simp [upPart, glue, h]

theorem eq_of_parts {y y' : Frame X.Ψ r} (h1 : lowPart X y = lowPart X y')
    (h2 : upPart X y = upPart X y') : y = y' := by
  funext τ a c
  by_cases h : c < a
  · rw [← lowPart_apply X y τ a c h, ← lowPart_apply X y' τ a c h, h1]
  · have := congrFun (congrFun (congrFun h2 τ) a) c
    simpa [upPart, h] using this

theorem contDiff_lowPart : ContDiff ℝ 1 (lowPart X) := by
  unfold lowPart
  refine (contDiff_piLp 2).2 fun j => ?_
  simp only
  fun_prop

theorem contDiff_upPart_entry (τ : X.Ψ) (a c : Fin r) :
    ContDiff ℝ 1 fun y => upPart X y τ a c := by
  unfold upPart
  split_ifs
  · exact contDiff_const
  · fun_prop

theorem continuous_upPart : Continuous (upPart X) :=
  continuous_pi fun τ => continuous_pi fun a => continuous_pi fun c =>
    (contDiff_upPart_entry X τ a c).continuous

def theta (x1 y : Frame X.Ψ r) : Frame X.Ψ r := rmul (cpt X x1 (lowPart X y)) (upPart X y)

theorem contDiff_theta (x1 : Frame X.Ψ r) : ContDiff ℝ 1 (theta X x1) := by
  refine contDiff_pi.2 fun τ => contDiff_pi.2 fun a => contDiff_pi.2 fun c => ?_
  show ContDiff ℝ 1 fun y => (mat (cpt X x1 (lowPart X y)) τ * mat (upPart X y) τ) a c
  simp only [Matrix.mul_apply]
  refine ContDiff.sum fun k _ => ContDiff.mul ?_ (contDiff_upPart_entry X τ k c)
  exact ((((OntoB.cd_cpt_entry X x1 τ a k).restrict_scalars ℝ).of_le (by simp)).comp
    (contDiff_lowPart X))

theorem measurableSet_Bor : MeasurableSet (Bor X.Ψ r) := by
  have : Bor X.Ψ r = ⋂ τ, ({b : Frame X.Ψ r | (mat b τ).det ≠ 0} ∩
      ⋂ a, ⋂ c, ⋂ (_ : c < a), {b : Frame X.Ψ r | b τ a c = 0}) := by
    ext b; simp [Bor]
  rw [this]
  refine MeasurableSet.iInter fun τ => MeasurableSet.inter ?_ ?_
  · have hM : Continuous fun b : Frame X.Ψ r => mat b τ := continuous_apply τ
    exact (isOpen_ne_fun hM.matrix_det continuous_const).measurableSet
  · refine MeasurableSet.iInter fun a => MeasurableSet.iInter fun c => MeasurableSet.iInter fun _ => ?_
    exact (isClosed_eq (by fun_prop) continuous_const).measurableSet

end

end GlobalTheory.FrameLoc

namespace GlobalTheory

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
  MeasureTheory Topology GlobalTheory.FrameLoc
open scoped ContDiff ENNReal Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem frame_measure_local :
    (∀ (r : ℕ) (X : Data E r) (R : ℝ), ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ g : V (nd X) → ℝ≥0∞, Measurable g → ∫⁻ y in {y : Frame X.Ψ r | ∀ τ a c, ¬ c < a → ‖y τ a c‖ ≤ R}, g (WithLp.toLp 2 fun j => y ((Fintype.equivFin (Ent X)).symm j).1 ((Fintype.equivFin (Ent X)).symm j).2.1.1 ((Fintype.equivFin (Ent X)).symm j).2.1.2) ≤ K * ∫⁻ z, g z) → (∀ (r : ℕ) (X : Data E r) (x1 : Frame X.Ψ r), IsOrth X x1 → ∀ b1 ∈ Bor X.Ψ r, ∃ U ∈ 𝓝 (rmul x1 b1), ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ G : Frame X.Ψ r → ℝ≥0∞, Measurable G → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x) → ∫⁻ x in U, G x ≤ K * ∫⁻ z, G (cpt X x1 z) ∂muF X x1) := by
  intro H r X x1 hx1 b1 hb1
  obtain ⟨Δ, zOf, bOf, hΔ, -, hz, hb, hsplit, huniq⟩ := lu_holds r X x1 hx1
  have h0 : (0 : V (nd X)) ∈ OmF X x1 := IW.zero_mem_OmF X x1 hx1
  obtain ⟨ρ, hρ, hball⟩ : ∃ ρ > 0, Metric.closedBall (0 : V (nd X)) ρ ⊆ OmF X x1 :=
    Metric.nhds_basis_closedBall.mem_iff.1 ((OntoB.isOpen_OmF X x1).mem_nhds h0)
  obtain ⟨z0, hz0, hmin⟩ := (isCompact_closedBall (0 : V (nd X)) ρ).exists_isMinOn
    ⟨0, Metric.mem_closedBall_self hρ.le⟩ (OntoB.densF_continuousOn.mono hball)
  have hc : 0 < densF X x1 z0 := OntoB.densF_pos (hball hz0)
  set R : ℝ := ‖b1‖ + 1 with hR
  set A : Set (Frame X.Ψ r) := {y | ∀ τ a c, ¬ c < a → ‖y τ a c‖ ≤ R} ∩
    (lowPart X ⁻¹' Metric.closedBall 0 ρ ∩ upPart X ⁻¹' Bor X.Ψ r) with hAdef
  have hS : MeasurableSet {y : Frame X.Ψ r | ∀ τ a c, ¬ c < a → ‖y τ a c‖ ≤ R} := by
    simp only [Set.setOf_forall]
    refine MeasurableSet.iInter fun τ => MeasurableSet.iInter fun a => MeasurableSet.iInter fun c =>
      MeasurableSet.iInter fun _ => ?_
    exact (isClosed_le (by fun_prop) continuous_const).measurableSet
  have hA : MeasurableSet A :=
    hS.inter (((contDiff_lowPart X).continuous.measurable Metric.isClosed_closedBall.measurableSet).inter
      ((continuous_upPart X).measurable (measurableSet_Bor X)))
  have hM : A ⊆ Metric.closedBall 0 (max R ρ) := by
    rintro y ⟨h1, h2, -⟩
    have hm : 0 ≤ max R ρ := hρ.le.trans (le_max_right _ _)
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hm]
    intro τ
    rw [pi_norm_le_iff_of_nonneg hm]
    intro a
    rw [pi_norm_le_iff_of_nonneg hm]
    intro c
    by_cases h : c < a
    · rw [← lowPart_apply X y τ a c h]
      refine le_trans (PiLp.norm_apply_le _ _) (le_trans ?_ (le_max_right _ _))
      exact mem_closedBall_zero_iff.1 h2
    · exact (h1 τ a c h).trans (le_max_left _ _)
  have hinj : Set.InjOn (theta X x1) A := by
    rintro y ⟨-, h2, h3⟩ y' ⟨-, h2', h3'⟩ he
    obtain ⟨-, e1, e2⟩ := huniq _ (hball h2) _ h3
    obtain ⟨-, e1', e2'⟩ := huniq _ (hball h2') _ h3'
    unfold theta at he
    exact eq_of_parts X (by rw [← e1, he, e1']) (by rw [← e2, he, e2'])
  haveI : (volume : Measure (Fin r → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Fin r → Fin r → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Frame X.Ψ r)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  obtain ⟨K1, hK1, hG1⟩ := lintegral_image_le_const volume (contDiff_theta X x1) hA hM hinj
  obtain ⟨K2, hK2, hG2⟩ := H r X R
  refine ⟨theta X x1 '' A, ?_, K1 * (K2 * (ENNReal.ofReal (densF X x1 z0))⁻¹), ?_, ?_⟩
  · have hu := huniq 0 h0 b1 hb1
    rw [IW.cpt_zero] at hu
    obtain ⟨u1, u2, u3⟩ := hu
    have hp : rmul x1 b1 ∈ X.dom := OrthogonalFrameDomain.rmul_mem_dom X (IW.orth_mem_dom X x1 hx1) hb1
    have hcell : {x | x ∈ X.dom ∧ Δ x ≠ 0} ∈ 𝓝 (rmul x1 b1) :=
      ((FourierCoefficientDomain.isOpen_dom X).inter (isOpen_ne_fun hΔ.continuous continuous_const)).mem_nhds ⟨hp, u1⟩
    have n1 : zOf ⁻¹' Metric.closedBall 0 ρ ∈ 𝓝 (rmul x1 b1) := by
      refine (hz.continuousOn.continuousAt hcell).preimage_mem_nhds ?_
      rw [u2]; exact Metric.closedBall_mem_nhds _ hρ
    have n2 : bOf ⁻¹' Metric.closedBall b1 1 ∈ 𝓝 (rmul x1 b1) := by
      refine (hb.continuousOn.continuousAt hcell).preimage_mem_nhds ?_
      rw [u3]; exact Metric.closedBall_mem_nhds _ one_pos
    filter_upwards [hcell, n1, n2] with x hx hx1' hx2
    obtain ⟨-, s2, s3⟩ := hsplit x hx.1 hx.2
    refine ⟨glue X (zOf x) (bOf x), ⟨?_, ?_, ?_⟩, ?_⟩
    · intro τ a c h
      have hn : ‖bOf x‖ ≤ R := by
        have : ‖bOf x - b1‖ ≤ 1 := by simpa [dist_eq_norm] using hx2
        have := norm_sub_norm_le (bOf x) b1
        linarith
      simp only [glue]
      rw [dif_neg h]
      exact ((norm_le_pi_norm _ c).trans ((norm_le_pi_norm _ a).trans (norm_le_pi_norm _ τ))).trans hn
    · simpa [lowPart_glue] using hx1'
    · simpa [upPart_glue X _ s2] using s2
    · unfold theta
      rw [lowPart_glue, upPart_glue X _ s2, ← s3]
  · refine ENNReal.mul_lt_top hK1 (ENNReal.mul_lt_top hK2 ?_)
    simpa using hc
  · intro G hG hinv
    set g : V (nd X) → ℝ≥0∞ := (Metric.closedBall 0 ρ).indicator fun z => G (cpt X x1 z) with hg
    have hGc : Measurable fun z => G (cpt X x1 z) := hG.comp (OntoB.cd_cpt X x1).continuous.measurable
    have hgm : Measurable g := hGc.indicator Metric.isClosed_closedBall.measurableSet
    refine (hG1 G).trans ?_
    rw [mul_assoc]
    gcongr
    have e1 : ∫⁻ y in A, G (theta X x1 y) = ∫⁻ y in A, g (lowPart X y) := by
      refine setLIntegral_congr_fun hA ?_
      rintro y ⟨-, h2, h3⟩
      simp only [hg]
      rw [Set.indicator_of_mem (Set.mem_preimage.1 h2)]
      exact hinv _ (hball h2) _ h3
    rw [e1]
    refine (lintegral_mono_set Set.inter_subset_left).trans ((hG2 g hgm).trans ?_)
    rw [mul_assoc]
    gcongr
    have hOm : MeasurableSet (OmF X x1) := (OntoB.isOpen_OmF X x1).measurableSet
    have hd : AEMeasurable (fun z => ENNReal.ofReal (densF X x1 z)) (volume.restrict (OmF X x1)) :=
      ((OntoB.densF_continuousOn (X := X) (x0 := x1)).aemeasurable hOm).ennreal_ofReal
    unfold muF
    rw [lintegral_withDensity_eq_lintegral_mul₀ hd hGc.aemeasurable, hg,
      lintegral_indicator Metric.isClosed_closedBall.measurableSet,
      ← lintegral_const_mul' _ _ (by simpa using hc)]
    refine le_trans ?_ (lintegral_mono_set hball)
    refine setLIntegral_mono' Metric.isClosed_closedBall.measurableSet fun z hz' => ?_
    have hle : ENNReal.ofReal (densF X x1 z0) ≤ ENNReal.ofReal (densF X x1 z) :=
      ENNReal.ofReal_le_ofReal (hmin hz')
    calc G (cpt X x1 z)
        = (ENNReal.ofReal (densF X x1 z0))⁻¹ * (ENNReal.ofReal (densF X x1 z0) * G (cpt X x1 z)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel (by simpa using hc) ENNReal.ofReal_ne_top, one_mul]
      _ ≤ _ := by
          simp only [Pi.mul_apply]
          gcongr

end GlobalTheory
