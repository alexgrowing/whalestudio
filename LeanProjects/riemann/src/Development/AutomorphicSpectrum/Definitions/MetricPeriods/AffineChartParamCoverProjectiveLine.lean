import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.ProjectiveLineLogLogRegularized
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLinePartitionContinuousCoe
import GroundTheory.HeightsAndTheta.Heights.Regularisation.IsOpenKappaOpenNeighbourhood
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.LineModel

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P MeasureTheory Matrix
open scoped ComplexOrder

def sysLog : AnSys 1 Unit where
  X := OnePoint ℂ
  A := p1
  Θ := fsPot
  L := fsPot
  s := projectiveLinePairSection
  nb := 1
  m := ![1]
  W := ![{OnePoint.infty}]
  potΘ := projLine_isSmoothPotential
  posΘ := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.projLine_fubiniStudy_isPosPot
  potL := projLine_isSmoothPotential
  sec := projLine_isHolomorphicSection
  snc := projLine_isSimpleNormalCrossing
  norm_le := logNormSec_nonpos
  th _ := fsPot
  ph _ := llw
  phT _ := llT
  C₅ := 1
  C := 2
  t₀ := T0
  sing _ := singWeight
  reg _ := projectiveLine_isRegFamily
  c2 _ := projectiveLine_isRegFamilyC2

theorem sysLog_degNum (w : Fin 1 → Unit) : sysLog.degNum w = 1 := projectiveLine_fubiniStudy_mass_one

theorem sysLog_degPoly : sysLog.degPoly = MvPolynomial.X () := by
  simp [AnSys.degPoly, formPoly, sysLog_degNum]

def flagTh (p : Unit × Fin 2) : LocPot (OnePoint ℂ) := if p.2 = 0 then fsPot else LocPot.ofFun fun _ => 0

theorem psh_fs_zero : IsPsh p1 (fsPot + LocPot.ofFun fun _ => 0) := by
  intro x j y hy w
  have := projLine_isPlurisubharmonic x j y ⟨hy.1, hy.2.1⟩ w
  show 0 ≤ levi (fun z => fsPot.φ x ((p1.chart j).symm z) + 0) y w
  simp only [add_zero]
  exact this

theorem sing_flag (p : Unit × Fin 2) : IsSingWeight p1 fsPot projectiveLinePairSection (flagTh p) (fun _ => 0) 0 := by
  unfold flagTh
  split_ifs
  · exact ⟨projLine_isSmoothPotential, fun _ => contDiffOn_const, fun x j y hy w => psh_fs_zero x j y ⟨hy.1, hy.2.1⟩ w,
      fun _ _ => by simp⟩
  · refine ⟨isPotential_ofFun _ _ fun _ => contDiffOn_const, fun _ => contDiffOn_const, fun x j y _ w => ?_,
      fun _ _ => by simp⟩
    show 0 ≤ levi (fun _ => (0 : ℝ) + 0) y w
    simp [levi]

theorem reg_flag (p : Unit × Fin 2) :
    IsRegFamily p1 fsPot fsPot projectiveLinePairSection (flagTh p) (fun _ => 0) (fun _ _ => 0) 1 (Real.exp (-Real.exp 1)) := by
  have h := (isRegFamilyInhabit p1 fsPot fsPot projectiveLinePairSection projLine_isSmoothPotential
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.projLine_fubiniStudy_isPosPot logNormSec_nonpos).1
  unfold flagTh
  split_ifs
  · exact h
  · refine ⟨h.1, h.2.1, fun t ht ht0 => ?_⟩
    obtain ⟨a, b, c, d, -, f⟩ := h.2.2 t ht ht0
    refine ⟨a, b, c, d, ?_, f⟩
    have hε : 0 ≤ epsT 1 t := by
      have h1 : Real.exp 1 ≤ Real.log (1 / t) := ell_ge ht ht0
      have h2 : 0 ≤ Real.log (Real.log (1 / t)) := Real.log_nonneg (by linarith [one_le_exp_one])
      unfold epsT
      rw [one_mul]
      exact div_nonneg h2 (by linarith [Real.exp_pos 1])
    intro x j y hy w
    have hyD : y ∈ (p1.chart j).target ∩ (p1.chart j).symm ⁻¹' fsPot.U x := ⟨hy.1, hy.2.2⟩
    have hc : ContDiffAt ℝ 2 (fsPot.φ x ∘ (p1.chart j).symm) y :=
      ((projLine_isSmoothPotential.1 x j).contDiffAt (((p1.chart j).isOpen_inter_preimage_symm
        (fsPot.isOpen_U x)).mem_nhds hyD)).of_le two_le_inf
    show 0 ≤ levi (fun z => (0 : ℝ) + 0 + epsT 1 t * fsPot.φ x ((p1.chart j).symm z)) y w
    rw [levi_add_smul (f := fun _ => (0 : ℝ) + 0) (g := fun z => fsPot.φ x ((p1.chart j).symm z)) (epsT 1 t)
      contDiffAt_const hc w]
    have h0 : levi (fun _ : Fin 1 → ℂ => (0 : ℝ) + 0) y w = 0 := by simp [levi]
    rw [h0, zero_add]
    exact mul_nonneg hε (projLine_isPlurisubharmonic x j y hyD w)

def sysFlag : AnSys 1 (Unit × Fin 2) :=
  { sysLog with
    th := flagTh, ph := fun _ _ => 0, phT := fun _ _ _ => 0, C₅ := 0, C := 1, t₀ := Real.exp (-Real.exp 1)
    sing := sing_flag, reg := reg_flag
    c2 := fun _ => (isRegFamilyInhabit p1 fsPot fsPot projectiveLinePairSection projLine_isSmoothPotential
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.projLine_fubiniStudy_isPosPot logNormSec_nonpos).2 }

def frame (_ : Unit) (y : OnePoint ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; crd0 y, 1]

theorem det_head_zero (hd : Fin 2 → ℝ) (g : Matrix (Fin 2) (Fin 2) ℂ) : (gramHead hd 0 g).det = 1 := by
  haveI : IsEmpty {a : Fin 2 // (a : ℕ) < 0} := ⟨fun a => by have := a.2; omega⟩
  exact Matrix.det_isEmpty

instance uniqueHead : Unique {a : Fin 2 // (a : ℕ) < 1} where
  default := ⟨0, by decide⟩
  uniq a := Subtype.ext (Fin.ext (by have := a.2; simp; omega))

theorem det_head_one (hd : Fin 2 → ℝ) (g : Matrix (Fin 2) (Fin 2) ℂ) : (gramHead hd 1 g).det = gramOf hd g 0 0 := by
  rw [Matrix.det_unique]; rfl

theorem det_head_two (hd : Fin 2 → ℝ) (g : Matrix (Fin 2) (Fin 2) ℂ) : (gramHead hd 2 g).det = (gramOf hd g).det :=
  Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (p := fun a : Fin 2 => (a : ℕ) < 2) fun a => a.2) _

theorem gram_frame_zero (hd : Fin 2 → ℝ) (y : OnePoint ℂ) :
    gramOf hd (frame () y) 0 0 = ((hd 0 + hd 1 * ‖crd0 y‖ ^ 2 : ℝ) : ℂ) := by
  simp [gramOf, frame, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, ← Complex.conj_mul']
  ring

theorem det_frame (y : OnePoint ℂ) : (frame () y).det = 1 := by simp [frame, Matrix.det_fin_two]

theorem det_gram_frame (hd : Fin 2 → ℝ) (y : OnePoint ℂ) : (gramOf hd (frame () y)).det = hd 0 * hd 1 := by
  simp [gramOf, det_frame]

theorem holo_frame {V : Set (OnePoint ℂ)} (hV : V ⊆ Set.range ((↑) : ℂ → OnePoint ℂ)) (τ : Unit) (a b : Fin 2) :
    p1.HoloOn V fun y => frame τ y a b := by
  fin_cases a <;> fin_cases b
  · exact holoOn_const _ 1
  · exact holoOn_const _ 0
  · exact holoOn_mono holomorphicOn_finiteCoord hV
  · exact holoOn_const _ 1

theorem immersion_frame : IsFlagImmersionAt p1 frame ((0 : ℂ) : OnePoint ℂ) := by
  intro k hk v hv
  fin_cases k
  · have h := hv () (i := 1) (j := 0) (by decide)
    have e : frame () ((0 : ℂ) : OnePoint ℂ) = 1 := by
      ext a b; fin_cases a <;> fin_cases b <;> simp [frame]
    rw [e, inv_one, one_mul, Matrix.of_apply] at h
    have e2 : (fun z : Fin 1 → ℂ => frame () ((p1.chart ((fun i => i) ⟨0, by decide⟩ : Fin p1.n)).symm z) 1 0) =
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0 := rfl
    rw [e2, ContinuousLinearMap.fderiv] at h
    funext i
    fin_cases i
    exact h
  · exact absurd rfl hk

theorem flagTh_zero : flagTh ((), 0) = fsPot := if_pos rfl
theorem flagTh_one : flagTh ((), 1) = LocPot.ofFun fun _ => 0 := if_neg (by decide)

theorem chart_flag (z : ℂ) :
    IsPeriodChart p1 2 sysFlag.potH (z : OnePoint ℂ) (Set.range ((↑) : ℂ → OnePoint ℂ)) frame := by
  refine ⟨OnePoint.isOpen_range_coe, ⟨z, rfl⟩, holo_frame subset_rfl, fun τ y _ => ⟨?_, ?_⟩, ?_⟩
  · rw [det_frame]; exact isUnit_one
  · have := (inFlagDomain_one 2).2
    convert this using 1
    haveI : IsEmpty {a : Fin 2 // (a : ℕ) < 2 - 2} := ⟨fun a => by have := a.2; omega⟩
    ext i; exact isEmptyElim i
  · rintro ⟨⟨⟩, i⟩
    refine ⟨fun _ => 0, holoOn_const _ 0, fun y _ => ?_⟩
    fin_cases i
    · show (flagTh ((), 0)).φ z y + 0 = gramLog (sigForm 2 2) 1 (frame () y) - gramLog (sigForm 2 2) 0 (frame () y) + 0
      rw [flagTh_zero, fsPot_φ_coe, gramLog, gramLog, det_head_zero, det_head_one, gram_frame_zero, Complex.norm_real]
      have : (0 : ℝ) ≤ 1 + ‖crd0 y‖ ^ 2 := by positivity
      simp [sigForm]
    · show (flagTh ((), 1)).φ z y + 0 = gramLog (sigForm 2 2) 2 (frame () y) - gramLog (sigForm 2 2) 0 (frame () y) + 0
      rw [flagTh_one, gramLog, gramLog, det_head_zero, det_head_two, det_gram_frame]
      simp [sigForm, LocPot.ofFun]

theorem sysFlag_uniformised : IsUniformised sysFlag.A sysFlag.open' 2 sysFlag.potH := by
  refine ⟨fun x hx => ?_, ((0 : ℂ) : OnePoint ℂ), fun h => ?_, _, _, chart_flag 0, immersion_frame⟩
  · have hx' : x ≠ OnePoint.infty := fun h => hx ((mem_boundary_projectiveLine x).2 h)
    obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.1 hx'
    exact ⟨_, _, chart_flag z⟩
  · exact OnePoint.coe_ne_infty 0 ((mem_boundary_projectiveLine _).1 h)

theorem sysFlag_degNum_zero : sysFlag.degNum (fun _ => ((), 0)) = 1 := by
  show mInt p1 (fun _ => flagTh ((), 0)) _ = 1
  rw [flagTh_zero]; exact projectiveLine_fubiniStudy_mass_one

def disc : Set (OnePoint ℂ) := ((↑) : ℂ → OnePoint ℂ) '' Metric.ball 0 1

def discPot (p : Unit × Fin 2) : LocPot (OnePoint ℂ) :=
  LocPot.ofFun fun y => if p.2 = 0 then -(1 / 2) * Real.log (1 - ‖crd0 y‖ ^ 2) else 0

theorem chart_disc {x : OnePoint ℂ} (hx : x ∈ disc) : IsPeriodChart p1 1 discPot x disc frame := by
  refine ⟨OnePoint.isOpen_image_coe.2 Metric.isOpen_ball, hx, holo_frame (Set.image_subset_range _ _),
    fun τ y hy => ⟨?_, ?_⟩, ?_⟩
  · rw [det_frame]; exact isUnit_one
  · obtain ⟨z, hz, rfl⟩ := hy
    have hz' : ‖z‖ < 1 := by simpa using hz
    have hp : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    show (-gramHead (sigForm 2 1) 1 (frame () (z : OnePoint ℂ))).PosDef
    have e : -gramHead (sigForm 2 1) 1 (frame () (z : OnePoint ℂ)) =
        Matrix.diagonal fun _ => ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by
      ext a b
      obtain rfl : a = default := Subsingleton.elim _ _
      obtain rfl : b = default := Subsingleton.elim _ _
      show -gramOf (sigForm 2 1) (frame () (z : OnePoint ℂ)) 0 0 = _
      rw [gram_frame_zero]
      simp [sigForm, neg_add_eq_sub]
    rw [e, Matrix.posDef_diagonal_iff]
    intro _
    exact_mod_cast hp
  · rintro ⟨⟨⟩, i⟩
    refine ⟨fun _ => 0, holoOn_const _ 0, fun y _ => ?_⟩
    fin_cases i
    · show -(1 / 2) * Real.log (1 - ‖crd0 y‖ ^ 2) =
        gramLog (sigForm 2 1) 2 (frame () y) - gramLog (sigForm 2 1) 1 (frame () y) + 0
      rw [gramLog, gramLog, det_head_two, det_head_one, gram_frame_zero, det_gram_frame, Complex.norm_real,
        Real.norm_eq_abs, Real.log_abs, ← Real.log_neg_eq_log (1 - _)]
      simp [sigForm, neg_add_eq_sub]
    · show (0 : ℝ) = gramLog (sigForm 2 1) 2 (frame () y) - gramLog (sigForm 2 1) 1 (frame () y) +
        gramLog (sigForm 2 1) 1 (frame () y) + 0
      rw [gramLog, det_head_two, det_gram_frame]
      simp [sigForm]

theorem disc_uniformised : IsUniformised p1 disc 1 discPot := by
  have h0 : ((0 : ℂ) : OnePoint ℂ) ∈ disc := ⟨0, by simp, rfl⟩
  exact ⟨fun x hx => ⟨_, _, chart_disc hx⟩, _, h0, _, _, chart_disc h0, immersion_frame⟩

theorem not_immersion_const : ¬ IsFlagImmersionAt p1 (fun (_ : Unit) _ => (1 : Matrix (Fin 2) (Fin 2) ℂ))
    ((0 : ℂ) : OnePoint ℂ) := by
  intro h
  have := h (0 : Fin 2) ⟨0, rfl⟩ 1 fun τ a b _ => by simp [Matrix.mul_apply]
  exact one_ne_zero (congrFun this 0)

theorem affine_chart_param_cover_projective_line : IsParamCover p1 (fun _ => Set.univ) (fun n => if n = 0 then Set.univ else ∅)
    (fun _ => projectiveLineChartAtZero.symm) := by
  refine ⟨fun _ => ⟨isOpen_univ, projectiveLineChartAtZero.continuousOn_symm, projectiveLineChartAtZero.symm.injOn, fun j => p1.holo (0 : Fin 2) j⟩,
    fun n => ⟨by by_cases hn : n = 0 <;> simp [hn], Set.subset_univ _⟩, fun n n' h => ?_, fun j => ?_⟩
  · by_cases hn : n = 0
    · have hn' : n' ≠ 0 := fun e => h (hn.trans e.symm)
      simp [hn']
    · simp [hn]
  · have hsub : (⋃ n : ℕ, projectiveLineChartAtZero.symm '' (if n = 0 then Set.univ else ∅ : Set (Fin 1 → ℂ)))ᶜ ⊆
        (Set.range ((↑) : ℂ → OnePoint ℂ))ᶜ := by
      refine Set.compl_subset_compl.2 ?_
      rintro _ ⟨z, rfl⟩
      exact Set.mem_iUnion.2 ⟨0, fun _ => z, by simp, rfl⟩
    refine measure_mono_null (t := {0}) ?_ (measure_singleton _)
    rintro w ⟨-, hw⟩
    have hw' := hsub hw
    fin_cases j
    · exact absurd ⟨w 0, rfl⟩ hw'
    · have : w 0 = 0 := by
        by_contra hc
        exact hw' (projLineChart1_symm_mem_range.2 hc)
      funext i
      fin_cases i
      exact this

theorem samePot_refl (U : Set (OnePoint ℂ)) (P : LocPot (OnePoint ℂ)) : SamePot p1 U P P :=
  fun _ _ => ⟨Set.univ, isOpen_univ, trivial, fun _ => 0, holoOn_const _ 0, fun _ _ => by simp⟩

end GlobalTheory.CompanionTheory.Ar.PB.LineModel
