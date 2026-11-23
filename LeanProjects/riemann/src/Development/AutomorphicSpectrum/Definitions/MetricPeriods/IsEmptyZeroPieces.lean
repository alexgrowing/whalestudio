import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.SimilitudeFactorFormGroupBoundedOfTestSupport
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.AffineChartParamCoverProjectiveLine
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GramSignatureTwoOneEntryZeroZero

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.PieceModel

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P MeasureTheory GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open GlobalTheory.CompanionTheory.Ar.PB.LineModel

instance uniqueLow : Unique (LowEnt Unit 2) where
  default := ((), ⟨(1, 0), by decide⟩)
  uniq := by decide

def q1 : LowEnt Unit 2 ≃ Fin 1 := Equiv.ofUnique _ _

theorem lowMat_two (q : LowEnt Unit 2 ≃ Fin 1) (z : Fin 1 → ℂ) (τ : Unit) : lowMat q z τ = !![1, 0; z 0, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [lowMat]
  congr 1; exact Subsingleton.elim _ _

theorem cellDom_two_two (q : LowEnt Unit 2 ≃ Fin 1) : cellDom 2 q = Set.univ := by
  refine Set.eq_univ_of_forall fun z τ => ?_
  rw [lowMat_two]
  exact (chart_flag (z 0)).2.2.2.1 () (z 0 : ℂ) ⟨_, rfl⟩

theorem cellDom_two_one (q : LowEnt Unit 2 ≃ Fin 1) : cellDom 1 q = {z | ‖z 0‖ < 1} := by
  ext z
  simp only [cellDom, Set.mem_setOf_eq, lowMat_two, Model.inFlagDomain_disc, forall_const]

theorem cellDens_two (j : ℕ) (q : LowEnt Unit 2 ≃ Fin 1) (z : Fin 1 → ℂ)
    (h : sigForm 2 j 0 + sigForm 2 j 1 * ‖z 0‖ ^ 2 ≠ 0) :
    cellDens j q z = ((sigForm 2 j 0 + sigForm 2 j 1 * ‖z 0‖ ^ 2) ^ 2)⁻¹ := by
  have e : (!![1, 0; z 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) = frame () ((z 0 : ℂ) : OnePoint ℂ) := rfl
  have h0 : gramLog (sigForm 2 j) 0 (frame () ((z 0 : ℂ) : OnePoint ℂ)) = 0 := by
    rw [gramLog, det_head_zero]; simp
  have h1 : gramLog (sigForm 2 j) 1 (frame () ((z 0 : ℂ) : OnePoint ℂ)) =
      (1 / 2) * Real.log (sigForm 2 j 0 + sigForm 2 j 1 * ‖z 0‖ ^ 2) := by
    rw [gramLog, det_head_one, gram_frame_zero, Complex.norm_real, Real.norm_eq_abs, Real.log_abs]; rfl
  simp only [cellDens, lowMat_two, e, Finset.prod_const, Finset.card_univ, Fintype.card_unit, pow_one,
    Fin.prod_univ_two, Fin.val_zero, Fin.val_one, h0, h1]
  have hp : 0 < (sigForm 2 j 0 + sigForm 2 j 1 * ‖z 0‖ ^ 2) ^ 2 := by positivity
  rw [← Real.exp_log hp, ← Real.exp_neg, Real.log_pow, ← Real.exp_add]
  congr 1; push_cast; ring

theorem cellDens_line (q : LowEnt Unit 2 ≃ Fin 1) (z : Fin 1 → ℂ) : cellDens 2 q z = ((1 + ‖z 0‖ ^ 2) ^ 2)⁻¹ := by
  have : sigForm 2 2 0 + sigForm 2 2 1 * ‖z 0‖ ^ 2 = 1 + ‖z 0‖ ^ 2 := by simp [sigForm]
  rw [cellDens_two 2 q z (by rw [this]; positivity), this]

theorem cellDens_disc (q : LowEnt Unit 2 ≃ Fin 1) (z : Fin 1 → ℂ) (hz : z ∈ cellDom 1 q) :
    cellDens 1 q z = ((1 - ‖z 0‖ ^ 2) ^ 2)⁻¹ := by
  rw [cellDom_two_one] at hz
  have hz' : ‖z 0‖ < 1 := hz
  have : sigForm 2 1 0 + sigForm 2 1 1 * ‖z 0‖ ^ 2 = -(1 - ‖z 0‖ ^ 2) := by simp [sigForm]; ring
  have hp : 0 < 1 - ‖z 0‖ ^ 2 := by nlinarith [norm_nonneg (z 0)]
  rw [cellDens_two 1 q z (by rw [this]; exact neg_ne_zero.2 hp.ne'), this, neg_sq]

def lineUnif : PieceUnif sysFlag 2 1 where
  q _ := q1
  π _ := projectiveLineChartAtZero.symm
  FF _ := Set.univ
  mem_open _ z _ h := OnePoint.coe_ne_infty (z 0) ((mem_boundary_projectiveLine _).1 h)
  param _ z _ := ⟨Set.univ, trivial, by rw [cellDom_two_two], affine_chart_param_cover_projective_line.1 0⟩
  pot _ z _ p := by
    refine ⟨fun _ => 0, analyticAt_const, Eventually.of_forall fun z' => ?_⟩
    rw [lowMat_two]
    obtain ⟨⟨⟩, i⟩ := p
    fin_cases i
    · show (flagTh ((), 0)).φ (z 0 : ℂ) (z' 0 : ℂ) + 0 = stepPot 2 2 0 !![1, 0; z' 0, 1] + 0
      rw [flagTh_zero, fsPot_φ_coe, Model.stepPot_pos_zero]
      simp
    · show (flagTh ((), 1)).φ (z 0 : ℂ) (z' 0 : ℂ) + 0 =
        gramLog (sigForm 2 2) 2 (frame () (z' 0 : ℂ)) - gramLog (sigForm 2 2) 0 (frame () (z' 0 : ℂ)) + 0
      rw [flagTh_one, gramLog, gramLog, det_head_zero, det_head_two, det_gram_frame]
      simp [sigForm, LocPot.ofFun]
  meas _ := MeasurableSet.univ
  sub _ := by rw [cellDom_two_two]
  inj _ := projectiveLineChartAtZero.symm.injOn
  disj k k' h := absurd (Subsingleton.elim k k') h
  cover := by
    intro j
    refine measure_mono_null ?_ (affine_chart_param_cover_projective_line.2.2.2 j)
    refine Set.inter_subset_inter_right _ (Set.preimage_mono (Set.compl_subset_compl.2 ?_))
    refine Set.iUnion_subset fun n => ?_
    exact (Set.image_mono (Set.subset_univ _)).trans (Set.subset_iUnion (fun _ : Fin 1 => projectiveLineChartAtZero.symm '' Set.univ) 0)

theorem lineUnif_vol : lineUnif.vol 0 = ∫⁻ z : Fin 1 → ℂ, ENNReal.ofReal (((1 + ‖z 0‖ ^ 2) ^ 2)⁻¹) := by
  show ∫⁻ z in Set.univ, ENNReal.ofReal (cellDens 2 q1 z) = _
  simp only [Measure.restrict_univ, cellDens_line]

theorem lineUnif_vol_pos : 0 < lineUnif.vol 0 := by
  rw [lineUnif_vol, lintegral_pos_iff_support (by fun_prop)]
  have : Function.support (fun z : Fin 1 → ℂ => ENNReal.ofReal (((1 + ‖z 0‖ ^ 2) ^ 2)⁻¹)) = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  rw [this]
  exact isOpen_univ.measure_pos _ Set.univ_nonempty

theorem lineUnif_vol_lt_top : lineUnif.vol 0 < ⊤ := by
  rw [lineUnif_vol]
  have h := (volume_preserving_funUnique (Fin 1) ℂ).lintegral_comp
    (f := fun w : ℂ => ENNReal.ofReal (((1 + ‖w‖ ^ 2) ^ 2)⁻¹)) (by fun_prop)
  have h2 : Integrable (fun w : ℂ => (1 + ‖w‖ ^ 2) ^ (-(4 : ℝ) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (by simp; norm_num)
  have h3 : (fun w : ℂ => (1 + ‖w‖ ^ 2) ^ (-(4 : ℝ) / 2)) = fun w : ℂ => ((1 + ‖w‖ ^ 2) ^ 2)⁻¹ := by
    funext w
    rw [show (-(4 : ℝ) / 2) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_natCast]
  rw [h3] at h2
  exact lt_of_eq_of_lt h h2.lintegral_lt_top

theorem exists_pieceUnif :
    ∃ (S : AnSys 1 (Unit × Fin 2)) (U : PieceUnif S 2 1), 0 < U.vol 0 ∧ U.vol 0 < ⊤ :=
  ⟨sysFlag, lineUnif, lineUnif_vol_pos, lineUnif_vol_lt_top⟩

theorem isEmpty_zero_pieces (j : ℕ) : IsEmpty (PieceUnif sysFlag j 0) := by
  refine ⟨fun U => ?_⟩
  have h := U.cover (0 : Fin 2)
  have e : (⋃ k : Fin 0, U.π k '' U.FF k) = ∅ := by simp
  rw [e, Set.compl_empty, Set.preimage_univ, Set.inter_univ] at h
  exact (isOpen_univ.measure_pos (volume : Measure (Fin 1 → ℂ)) Set.univ_nonempty).ne' h

end GlobalTheory.CompanionTheory.Ar.Cmp.PieceModel
