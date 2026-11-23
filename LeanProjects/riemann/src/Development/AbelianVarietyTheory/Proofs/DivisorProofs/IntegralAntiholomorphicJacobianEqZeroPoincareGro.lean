import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogCutoffCoordinateHyperplanesPoincareBounStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDetLeOfWeightedEntryBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnOffCoordinateHyperplanesOfPoincareBoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDbarJacobianDetEqZeroOfCompactSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenOffCoordinateHyperplanesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareVolumeIntegrableOnCompactPuncturedPolydiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareCoordinateLengthMemIccAndPosStatement

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem continuousOn_det_dbar {n : ℕ} {Ω : Set (V n)} (hΩ : IsOpen Ω) {g : Fin n → V n → ℂ}
    (hg : ∀ i, ContDiffOn ℝ 2 (g i) Ω) :
    ContinuousOn (fun v => (Matrix.of fun i b => dbar (g i) v (coordVec b)).det) Ω := by
  have he : ∀ i (w : V n), ContinuousOn (fun v => dbar (g i) v w) Ω := by
    intro i w
    have hd := (hg i).continuousOn_fderiv_of_isOpen hΩ one_le_two
    simp only [dbar_apply]
    exact ((hd.clm_apply continuousOn_const).add
      ((hd.clm_apply continuousOn_const).const_smul Complex.I)).const_smul (1 / 2 : ℂ)
  have hM : ContinuousOn (fun v => Matrix.of fun i b => dbar (g i) v (coordVec b)) Ω :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun b => he i _
  exact (continuous_id.matrix_det).comp_continuousOn hM

theorem det_dbar_eq_zero_of_row {n : ℕ} {g : Fin n → V n → ℂ} {v : V n} (j : Fin n)
    (h : g j =ᶠ[𝓝 v] fun _ => 0) :
    (Matrix.of fun i b => dbar (g i) v (coordVec b)).det = 0 := by
  apply Matrix.det_eq_zero_of_row_eq_zero j
  intro b
  simp [dbar_congr h]

theorem integral_det_dbar_eq_zero_of_poincare : ∀ {n : ℕ} (S : Finset (Fin n)) (U K : Set (V n)) (f : Fin n → V n → ℂ)
    (j : Fin n) (u : Equiv.Perm (Fin n)) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U →
    (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ i, ContDiffOn ℝ 2 (f i) (offHyp S U)) →
    (∀ v ∈ offHyp S U, v ∉ K → f j v = 0) → (∀ v ∈ offHyp S U, v ∈ K → ‖f j v‖ * poinWt S v (u j) ≤ c) →
    (∀ v ∈ offHyp S U, v ∈ K → ∀ i b, ‖dbar (f i) v (coordVec b)‖ * (poinWt S v (u i) * poinWt S v b) ≤ c) →
    IntegrableOn (fun v => (Matrix.of fun i b => dbar (f i) v (coordVec b)).det) (offHyp S U) ∧
      ∫ v in offHyp S U, (Matrix.of fun i b => dbar (f i) v (coordVec b)).det = 0 := by
  intro n S U K f j u c hU hK hKU hsmall hf hf0 hfb hdb
  have hΩ : IsOpen (offHyp S U) := GlobalTheory.T.isOpen_offCoordinateHyperplanes S U hU
  have hΩm : MeasurableSet (offHyp S U) := hΩ.measurableSet
  have hKc : IsClosed K := hK.isClosed
  have hwt : ∀ v ∈ offHyp S U, ∀ a, 0 < poinWt S v a := fun v hv =>
    (GlobalTheory.T.poincareCoordinateLength_mem_Icc_and_pos S v (hsmall v hv.1)).2 hv.2
  have hoff : ∀ g : Fin n → V n → ℂ, (∀ v ∈ offHyp S U, v ∉ K → g j v = 0) → ∀ v ∈ offHyp S U, v ∉ K →
      (Matrix.of fun i b => dbar (g i) v (coordVec b)).det = 0 := fun g hg v hv hvK =>
    det_dbar_eq_zero_of_row j (Filter.eventually_of_mem ((hΩ.sdiff hKc).mem_nhds ⟨hv, hvK⟩)
      fun x hx => hg x hx.1 hx.2)
  have hbd : ∀ (g : Fin n → V n → ℂ) (c' : ℝ), (∀ v ∈ offHyp S U, v ∈ K → ∀ i b,
      ‖dbar (g i) v (coordVec b)‖ * (poinWt S v (u i) * poinWt S v b) ≤ c') → ∀ v ∈ offHyp S U, v ∈ K →
      ‖(Matrix.of fun i b => dbar (g i) v (coordVec b)).det‖ ≤
        (n.factorial : ℝ) * |c'| ^ n * ∏ a, (poinWt S v a)⁻¹ ^ 2 :=
    fun g c' h v hv hvK => GlobalTheory.T.norm_det_le_of_weighted_entry_bound _ u _ c' (hwt v hv) (h v hv hvK)
  have hint := GlobalTheory.T.integrableOn_offCoordinateHyperplanes_of_poincareBound S U K (fun v => (Matrix.of fun i b => dbar (f i) v (coordVec b)).det) _ hU hK hKU hsmall
    (continuousOn_det_dbar hΩ hf) (hoff f hf0) (hbd f c hdb)
  refine ⟨hint, ?_⟩
  obtain ⟨C, χ, hχs, hχ01, hχ0, hχ1, hχd⟩ := GlobalTheory.T.exists_logCutoff_coordinateHyperplanes_poincareBound S
  let F : ℕ → Fin n → V n → ℂ := fun k => Function.update f j (fun x => (χ k x : ℂ) * f j x)
  have hFj : ∀ k, F k j = fun x => (χ k x : ℂ) * f j x := fun k => by simp [F]
  have hFi : ∀ k i, i ≠ j → F k i = f i := fun k i hi => by simp [F, Function.update_of_ne hi]
  have hχC : ∀ k, ContDiffOn ℝ 2 (fun x => (χ k x : ℂ)) (offHyp S U) := fun k =>
    (Complex.ofRealCLM.contDiff.comp (by exact_mod_cast contDiff_infty.1 (hχs k) 2)).contDiffOn
  have hFs : ∀ k i, ContDiffOn ℝ 2 (F k i) (offHyp S U) := by
    intro k i
    by_cases hi : i = j
    · rw [hi, hFj]; exact (hχC k).mul (hf j)
    · rw [hFi k i hi]; exact hf i
  have hF0 : ∀ k, ∀ v ∈ offHyp S U, v ∉ K → F k j v = 0 := fun k v hv hvK => by
    rw [hFj]; simp [hf0 v hv hvK]
  have hzero : ∀ k, ∫ v in offHyp S U, (Matrix.of fun i b => dbar (F k i) v (coordVec b)).det = 0 := by
    intro k
    have hsub : K ∩ tsupport (χ k) ⊆ offHyp S U := by
      rintro v ⟨hvK, hvt⟩
      refine ⟨hKU hvK, fun a ha h0 => ?_⟩
      exact (notMem_tsupport_iff_eventuallyEq.2 (hχ0 k v ⟨a, ha, h0⟩)) hvt
    refine GlobalTheory.T.integral_dbarJacobian_det_eq_zero_of_compactSupport (offHyp S U) (K ∩ tsupport (χ k)) (F k) j hΩ (hK.inter_right (isClosed_tsupport _))
      hsub (hFs k) ?_
    intro v hv hvn
    by_cases hvK : v ∈ K
    · have : v ∉ tsupport (χ k) := fun h => hvn ⟨hvK, h⟩
      rw [hFj]; simp [image_eq_zero_of_notMem_tsupport this]
    · exact hF0 k v hv hvK
  have hFb : ∀ k, ∀ v ∈ offHyp S U, v ∈ K → ∀ i b,
      ‖dbar (F k i) v (coordVec b)‖ * (poinWt S v (u i) * poinWt S v b) ≤ |c| + |C| * |c| := by
    intro k v hv hvK i b
    have hw := hwt v hv
    have hCc : 0 ≤ |C| * |c| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    by_cases hi : i = j
    · rw [hi, hFj]
      have hvn := hΩ.mem_nhds hv
      rw [dbar_mul (a := fun x => (χ k x : ℂ)) (b := f j)
        (((hχC k).differentiableOn two_ne_zero).differentiableAt hvn)
        (((hf j).differentiableOn two_ne_zero).differentiableAt hvn) (coordVec b)]
      have h1 := hdb v hv hvK j b
      have h2 := hχd k v b
      have h3 := hfb v hv hvK
      have hχv := hχ01 k v
      have hp : 0 ≤ poinWt S v (u j) * poinWt S v b := mul_nonneg (hw _).le (hw _).le
      have hA : 0 ≤ ‖dbar (f j) v (coordVec b)‖ * (poinWt S v (u j) * poinWt S v b) :=
        mul_nonneg (norm_nonneg _) hp
      have hB : 0 ≤ ‖dbar (fun x => (χ k x : ℂ)) v (coordVec b)‖ * poinWt S v b :=
        mul_nonneg (norm_nonneg _) (hw _).le
      have hE : 0 ≤ ‖f j v‖ * poinWt S v (u j) := mul_nonneg (norm_nonneg _) (hw _).le
      calc ‖(χ k v : ℂ) * dbar (f j) v (coordVec b) + dbar (fun x => (χ k x : ℂ)) v (coordVec b) * f j v‖ *
            (poinWt S v (u j) * poinWt S v b)
          ≤ (‖(χ k v : ℂ) * dbar (f j) v (coordVec b)‖ + ‖dbar (fun x => (χ k x : ℂ)) v (coordVec b) * f j v‖) *
            (poinWt S v (u j) * poinWt S v b) := mul_le_mul_of_nonneg_right (norm_add_le _ _) hp
        _ = χ k v * (‖dbar (f j) v (coordVec b)‖ * (poinWt S v (u j) * poinWt S v b)) +
            (‖dbar (fun x => (χ k x : ℂ)) v (coordVec b)‖ * poinWt S v b) * (‖f j v‖ * poinWt S v (u j)) := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hχv.1]; ring
        _ ≤ |c| + |C| * |c| := by
          refine add_le_add ?_ ?_
          · exact (mul_le_of_le_one_left hA hχv.2).trans (h1.trans (le_abs_self c))
          · exact mul_le_mul (h2.trans (le_abs_self C)) (h3.trans (le_abs_self c)) hE (abs_nonneg _)
    · rw [hFi k i hi]
      exact (hdb v hv hvK i b).trans ((le_abs_self c).trans (le_add_of_nonneg_right hCc))
  let bound : V n → ℝ := K.indicator fun v =>
    (n.factorial : ℝ) * |(|c| + |C| * |c|)| ^ n * ∏ a, (poinWt S v a)⁻¹ ^ 2
  have hbint : Integrable bound (volume.restrict (offHyp S U)) := by
    rw [integrable_indicator_iff hKc.measurableSet, IntegrableOn,
      Measure.restrict_restrict hKc.measurableSet]
    exact IntegrableOn.mono_set ((GlobalTheory.T.poincare_volume_integrableOn_compact_punctured_polydisc S K hK fun v hv => hsmall v (hKU hv)).const_mul
      ((n.factorial : ℝ) * |(|c| + |C| * |c|)| ^ n)) Set.inter_subset_left
  have hmeas : ∀ k, AEStronglyMeasurable (fun v => (Matrix.of fun i b => dbar (F k i) v (coordVec b)).det)
      (volume.restrict (offHyp S U)) := fun k =>
    (continuousOn_det_dbar hΩ (hFs k)).aestronglyMeasurable hΩm
  have hle : ∀ k, ∀ᵐ v ∂(volume.restrict (offHyp S U)),
      ‖(Matrix.of fun i b => dbar (F k i) v (coordVec b)).det‖ ≤ bound v := by
    intro k
    refine (ae_restrict_iff' hΩm).2 (Filter.Eventually.of_forall fun v hv => ?_)
    by_cases hvK : v ∈ K
    · simp only [bound, Set.indicator_of_mem hvK]
      exact hbd (F k) _ (hFb k) v hv hvK
    · simp only [bound, Set.indicator_of_notMem hvK]
      rw [hoff (F k) (hF0 k) v hv hvK, norm_zero]
  have hlim : ∀ᵐ v ∂(volume.restrict (offHyp S U)),
      Tendsto (fun k => (Matrix.of fun i b => dbar (F k i) v (coordVec b)).det) atTop
        (𝓝 ((Matrix.of fun i b => dbar (f i) v (coordVec b)).det)) := by
    refine (ae_restrict_iff' hΩm).2 (Filter.Eventually.of_forall fun v hv => ?_)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hχ1 v hv.2] with k hk
    congr 1
    ext i b
    by_cases hi : i = j
    · simp only [Matrix.of_apply, hi, hFj]
      rw [dbar_congr (f := f j) (g := fun x => (χ k x : ℂ) * f j x) (hk.mono fun x hx => by simp [hx])]
    · simp only [Matrix.of_apply, hFi k i hi]
  have hT := tendsto_integral_of_dominated_convergence bound hmeas hbint hle hlim
  have h0 : (fun k => ∫ v in offHyp S U, (Matrix.of fun i b => dbar (F k i) v (coordVec b)).det) = fun _ => 0 :=
    funext hzero
  rw [h0] at hT
  exact tendsto_nhds_unique hT tendsto_const_nhds

end GlobalTheory.GoodTop
