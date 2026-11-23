import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfJ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OmFConnPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.KronValue

theorem lintegral_ball_lt_top {n : ℕ} {Ω : Set (V n)} (hΩ : IsOpen Ω) {d w g H : V n → ℝ}
    (hd : ContinuousOn d Ω) (hdpos : ∀ z ∈ Ω, 0 < d z)
    (hw : ContinuousOn w Ω) (hwpos : ∀ z ∈ Ω, 0 < w z) {ρ : ℝ} (hρ : 0 < ρ)
    (hB : Metric.closedBall (0 : V n) ρ ⊆ Ω) (hg : ∀ z, 0 ≤ g z)
    (hH : ∀ z ∈ Metric.ball (0 : V n) ρ, H z = g z * w z)
    (hfin : ∫⁻ z, ENNReal.ofReal (H z)
      ∂((volume.restrict Ω).withDensity fun z => ENNReal.ofReal (d z)) < ⊤) :
    ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal (g z) < ⊤ := by
  have hm : AEMeasurable (fun z => ENNReal.ofReal (d z)) (volume.restrict Ω) :=
    (hd.aemeasurable hΩ.measurableSet).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hm
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hfin
  obtain ⟨z0, hz0, hmin⟩ := (isCompact_closedBall (0 : V n) ρ).exists_isMinOn
    ⟨0, Metric.mem_closedBall_self hρ.le⟩ ((hd.mul hw).mono hB)
  set c := d z0 * w z0 with hc
  have hcpos : 0 < c := mul_pos (hdpos _ (hB hz0)) (hwpos _ (hB hz0))
  have hsub : Metric.ball (0 : V n) ρ ⊆ Ω := Metric.ball_subset_closedBall.trans hB
  calc ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal (g z)
      ≤ ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal c⁻¹ *
          ((fun z => ENNReal.ofReal (d z)) * fun z => ENNReal.ofReal (H z)) z := by
        refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
        have h1 : c ≤ d z * w z := hmin (Metric.ball_subset_closedBall hz)
        simp only [Pi.mul_apply]
        rw [← ENNReal.ofReal_mul (hdpos z (hsub hz)).le, ← ENNReal.ofReal_mul (inv_pos.2 hcpos).le,
          hH z hz]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [le_inv_mul_iff₀ hcpos]
        nlinarith [mul_le_mul_of_nonneg_right h1 (hg z)]
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ z in Metric.ball (0 : V n) ρ,
          ((fun z => ENNReal.ofReal (d z)) * fun z => ENNReal.ofReal (H z)) z :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ((lintegral_mono_set hsub).trans_lt hfin)

theorem lintegral_lt_top_of_cutoff {n : ℕ} {Ω : Set (V n)} (hΩ : IsOpen Ω) {d w S : V n → ℝ}
    {χ F : V n → ℂ} (hd : ContinuousOn d Ω)
    (hw : ContinuousOn w Ω) (hwpos : ∀ z ∈ Ω, 0 < w z) {δ : ℝ}
    (hB : Metric.closedBall (0 : V n) δ ⊆ Ω) (hχ : Continuous χ) (hχ0 : ∀ z, δ ≤ ‖z‖ → χ z = 0)
    {M : ℝ} (hM : ∀ z ∈ Ω, S z ≤ M) (hS : ∀ᵐ z ∂(volume.restrict Ω), 0 < S z) {p : ℝ} (hp : 0 ≤ p)
    (hfin : ∫⁻ z, ENNReal.ofReal (‖χ z - F z‖ ^ 2 * w z * S z ^ (-p))
      ∂((volume.restrict Ω).withDensity fun z => ENNReal.ofReal (d z)) < ⊤) :
    ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 * w z)
      ∂((volume.restrict Ω).withDensity fun z => ENNReal.ofReal (d z)) < ⊤ := by
  set μ := (volume.restrict Ω).withDensity fun z => ENNReal.ofReal (d z) with hμ
  have hK := isCompact_closedBall (0 : V n) δ
  have hKm : MeasurableSet (Metric.closedBall (0 : V n) δ) := hK.measurableSet
  have hμK : μ (Metric.closedBall 0 δ) < ⊤ := by
    rw [hμ, withDensity_apply _ hKm, Measure.restrict_restrict hKm, Set.inter_eq_left.2 hB]
    exact Integrable.lintegral_lt_top ((hd.mono hB).integrableOn_compact hK)
  obtain ⟨B, hBd⟩ := hK.exists_bound_of_continuousOn
    (f := fun z => 2 * (‖χ z‖ ^ 2 * w z))
    (continuousOn_const.mul ((hχ.norm.pow 2).continuousOn.mul (hw.mono hB)))
  have hac : μ ≪ volume.restrict Ω := withDensity_absolutelyContinuous _ _
  have hae : ∀ᵐ z ∂μ, ENNReal.ofReal (‖F z‖ ^ 2 * w z) ≤
      (Metric.closedBall (0 : V n) δ).indicator (fun _ => ENNReal.ofReal B) z +
        ENNReal.ofReal (2 * M ^ p) * ENNReal.ofReal (‖χ z - F z‖ ^ 2 * w z * S z ^ (-p)) := by
    filter_upwards [hac.ae_le hS, hac.ae_le (ae_restrict_mem hΩ.measurableSet)] with z hz hzΩ
    have hz : 0 < S z := hz
    have hzΩ : z ∈ Ω := hzΩ
    have hMpos : 0 < M := hz.trans_le (hM z hzΩ)
    have hwz := hwpos z hzΩ
    have h1 : ENNReal.ofReal (2 * (‖χ z‖ ^ 2 * w z)) ≤
        (Metric.closedBall (0 : V n) δ).indicator (fun _ => ENNReal.ofReal B) z := by
      by_cases hzK : z ∈ Metric.closedBall (0 : V n) δ
      · rw [Set.indicator_of_mem hzK]
        exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hBd z hzK))
      · have : δ ≤ ‖z‖ := by
          rw [mem_closedBall_zero_iff, not_le] at hzK; exact hzK.le
        simp [hχ0 z this]
    have h2 : 1 ≤ M ^ p * S z ^ (-p) := by
      rw [Real.rpow_neg hz.le, ← div_eq_mul_inv, one_le_div (Real.rpow_pos_of_pos hz p)]
      exact Real.rpow_le_rpow hz.le (hM z hzΩ) hp
    have h3 : ‖F z‖ ^ 2 ≤ 2 * ‖χ z‖ ^ 2 + 2 * ‖χ z - F z‖ ^ 2 := by
      have : ‖F z‖ ≤ ‖χ z‖ + ‖χ z - F z‖ := by
        simpa using norm_sub_le (χ z) (χ z - F z)
      nlinarith [norm_nonneg (F z), norm_nonneg (χ z), norm_nonneg (χ z - F z),
        sq_nonneg (‖χ z‖ - ‖χ z - F z‖)]
    have hA : 0 ≤ ‖χ z - F z‖ ^ 2 * w z := by positivity
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine le_trans ?_ (add_le_add_left h1 _)
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (ENNReal.ofReal_add (by positivity)
      (mul_nonneg (by positivity) (mul_nonneg hA (Real.rpow_nonneg hz.le _)))).le
    nlinarith [mul_le_mul_of_nonneg_right h3 hwz.le, mul_le_mul_of_nonneg_right h2 hA]
  refine (lintegral_mono_ae hae).trans_lt ?_
  rw [lintegral_add_left (measurable_const.indicator hKm), lintegral_indicator_const hKm,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμK,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem pnorm_eq {r : ℕ} (X : Data E r) (L : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm L P x = ‖P x‖ * X.nfac L x := rfl

theorem value_and_integrability : (VanishAtSStatement (E := E)) → (∀ (r : ℕ) (X : Data E r) (la L : Wt X.Ψ r) (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ) (ψ : Frame X.Ψ r → ℝ) (x0 : Frame X.Ψ r) (bb ε δ : ℝ) (χ F : V (nd X) → ℂ), 0 < nd X → IsOrth X x0 → X.IsBddSec L w0 → (∀ k, X.IsBddSec L (s k)) → ContinuousOn ψ X.dom → (∃ C : ℝ, ∀ x ∈ X.dom, ψ x ≤ C) → 0 ≤ bb → 0 < ε → Metric.closedBall (0 : V (nd X)) δ ⊆ OmF X x0 → Continuous χ → (∀ z, ‖z‖ ≤ ε → χ z = 1) → (∀ z, δ ≤ ‖z‖ → χ z = 0) → DifferentiableOn ℂ F (OmF X x0) → ∫⁻ z, ENNReal.ofReal (‖χ z - F z‖ ^ 2 * Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) / kaF X x0 bb z * (∑ k, X.pnorm L (s k) (cpt X x0 z) ^ 2) ^ (-(nd X : ℝ))) ∂muF X x0 < ⊤ → w0 x0 ≠ 0 → (∀ k, s k x0 = 0) → (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => s k (cpt X (x0) z) / w0 (cpt X (x0) z) : V (nd X))) 0).det ≠ 0 → F 0 = 1 ∧ InAt X x0 (X.dom.indicator fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x)))) bb F ∧ ∀ C : Set (Frame X.Ψ r), IsCompact C → C ⊆ X.dom → ∫⁻ z in sat X x0 C, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z))) ∂muF X x0 < ⊤) := by
  intro hV r X la L w0 s ψ x0 bb ε δ χ F hn ho hw0 hs hψ hψC hbb hε hB hχ hχ1 hχ0 hF hfin hw0x hsx hdet
  have hΩ := OntoB.isOpen_OmF X x0
  have h0 : (0 : V (nd X)) ∈ OmF X x0 := IW.zero_mem_OmF X x0 ho
  have hcpt : Continuous (cpt X x0) := (OntoB.cd_cpt X x0).continuous
  set w : V (nd X) → ℝ := fun z =>
    Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) / kaF X x0 bb z with hwdef
  have hka : ∀ z, 0 < kaF X x0 bb z := fun z => Real.exp_pos _
  have hwpos : ∀ z ∈ OmF X x0, 0 < w z := fun z _ => div_pos (Real.exp_pos _) (hka z)
  have hw : ContinuousOn w (OmF X x0) := by
    have h1 := OntoE.expPhla_cont X x0 la
    have h2 : ContinuousOn (fun z => Real.exp (-ψ (cpt X x0 z))) (OmF X x0) :=
      Real.continuous_exp.comp_continuousOn (hψ.comp hcpt.continuousOn fun _ hz => hz).neg
    have h3 : ContinuousOn (kaF X x0 bb) (OmF X x0) := fun z hz =>
      (OntoB.ka_contDiffAt bb hz).continuousAt.continuousWithinAt
    refine ((h1.mul h2).div h3 fun z _ => (hka z).ne').congr fun z _ => ?_
    simp only [hwdef, Pi.div_apply, Pi.mul_apply]
    rw [← Real.exp_add, neg_add]
  have hfin' : ∫⁻ z, ENNReal.ofReal (‖χ z - F z‖ ^ 2 * w z *
      (∑ k, X.pnorm L (s k) (cpt X x0 z) ^ 2) ^ (-(nd X : ℝ))) ∂muF X x0 < ⊤ := by
    simpa only [hwdef, mul_div_assoc] using hfin
  have hS : ∀ z, ∑ k, X.pnorm L (s k) (cpt X x0 z) ^ 2 =
      (∑ k, ‖s k (cpt X x0 z)‖ ^ 2) * X.nfac L (cpt X x0 z) ^ 2 := fun z => by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by rw [pnorm_eq, mul_pow]
  have hsd : ∀ k, DifferentiableOn ℂ (fun z => s k (cpt X x0 z)) (OmF X x0) := fun k =>
    OntoB.hol_comp X x0 (hs k).1.1
  have hmain : ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 * w z) ∂muF X x0 < ⊤ := by
    choose C hC using fun k => (hs k).2
    refine lintegral_lt_top_of_cutoff hΩ OntoB.densF_continuousOn hw hwpos hB hχ hχ0
      (M := ∑ k, C k ^ 2) (fun z hz => Finset.sum_le_sum fun k _ => ?_) ?_ (Nat.cast_nonneg _) hfin'
    · have hp : 0 ≤ X.pnorm L (s k) (cpt X x0 z) := by
        rw [pnorm_eq]; exact mul_nonneg (norm_nonneg _) (OntoE.nfac_pos X x0 hz).le
      exact pow_le_pow_left₀ hp (hC k _ hz) 2
    · obtain ⟨k, hk⟩ := HE.coord_ne_of_det hn hdet
      have hne : ∃ z ∈ OmF X x0, s k (cpt X x0 z) ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hk
        filter_upwards [hΩ.mem_nhds h0] with z hz
        simp [hall z hz]
      have hnull := OntoD.null_zero hΩ (OmFConnStatement_holds r X x0 ho) (hsd k) hne
      rw [ae_restrict_iff' hΩ.measurableSet]
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with z hz hzΩ
      have hsk : s k (cpt X x0 z) ≠ 0 := fun h => hz ⟨hzΩ, h⟩
      rw [hS]
      refine mul_pos ?_ (pow_pos (OntoE.nfac_pos X x0 hzΩ) 2)
      exact Finset.sum_pos' (fun _ _ => by positivity)
        ⟨k, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hsk) 2⟩
  have haeΩ : ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hΩ.measurableSet)
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨Δ, zOf, bOf, -, -, -, -, -, hLU⟩ := lu_holds r X x0 ho
    have hz : ∀ z ∈ OmF X x0, zOf (cpt X x0 z) = z := fun z hz => by
      have := (hLU z hz _ (ExtFPf.oneF_mem X)).2.1
      rwa [ExtFPf.rmul_oneF] at this
    obtain ⟨ρ0, hρ0, hρB⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hΩ.mem_nhds h0)
    set ρ := min ρ0 ε
    have hρ : 0 < ρ := lt_min hρ0 hε
    have hcB : Metric.closedBall (0 : V (nd X)) ρ ⊆ OmF X x0 :=
      (Metric.closedBall_subset_closedBall (min_le_left _ _)).trans hρB
    have hbB : Metric.ball (0 : V (nd X)) ρ ⊆ OmF X x0 := Metric.ball_subset_closedBall.trans hcB
    have key := hV r X x0 hn ho (IW.orth_mem_dom X x0 ho) (fun y => 1 - F (zOf y)) w0 s ρ hρ
      (((differentiableOn_const (1 : ℂ)).sub (hF.mono hbB)).congr fun z hz' => by
        simp [hz z (hbB hz')])
      (fun k => (hsd k).mono hbB) ((OntoB.hol_comp X x0 hw0.1.1).mono hbB) hw0x hsx hdet ?_
    · have h00 : zOf x0 = 0 := by simpa [IW.cpt_zero] using hz 0 h0
      simp only [h00] at key
      exact (sub_eq_zero.1 key).symm
    · refine lintegral_ball_lt_top hΩ OntoB.densF_continuousOn (fun z => OntoB.densF_pos)
        (w := fun z => w z * (X.nfac L (cpt X x0 z) ^ 2) ^ (-(nd X : ℝ))) ?_ ?_ hρ hcB ?_ ?_ hfin'
      · exact hw.mul (((OntoE.nfac_cont X x0 L).pow 2).rpow_const fun z hz' =>
          Or.inl (pow_pos (OntoE.nfac_pos X x0 hz') 2).ne')
      · exact fun z hz' => mul_pos (hwpos z hz')
          (Real.rpow_pos_of_pos (pow_pos (OntoE.nfac_pos X x0 hz') 2) _)
      · intro z; positivity
      · intro z hz'
        have : ‖z‖ ≤ ε := (mem_ball_zero_iff.1 hz').le.trans (min_le_right _ _)
        rw [hS, Real.mul_rpow (by positivity) (by positivity), hχ1 z this, hz z (hbB hz')]
        ring
  · unfold InAt
    refine lt_of_eq_of_lt (lintegral_congr_ae ?_) hmain
    filter_upwards [haeΩ] with z hz
    have hz' : cpt X x0 z ∈ X.dom := hz
    rw [Set.indicator_of_mem hz', ← ENNReal.ofReal_mul (div_nonneg (by positivity) (hka z).le)]
    congr 1
    simp only [hwdef]; ring
  · intro C _ _
    obtain ⟨A, hA⟩ := hψC
    refine (lintegral_mono' Measure.restrict_le_self le_rfl).trans_lt ?_
    refine lt_of_le_of_lt (lintegral_mono_ae (g := fun z => ENNReal.ofReal (Real.exp A) *
      ENNReal.ofReal (‖F z‖ ^ 2 * w z)) ?_) ?_
    · filter_upwards [haeΩ] with z hz
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [mul_left_comm]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      simp only [hwdef, kaF]
      rw [← Real.exp_sub, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      nlinarith [hA _ hz, mul_nonneg hbb (ExF.rhF_nonneg X x0 ho hz)]
    · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmain

end GlobalTheory.KronValue
