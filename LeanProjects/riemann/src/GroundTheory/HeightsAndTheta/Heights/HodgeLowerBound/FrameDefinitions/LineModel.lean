import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.LineMu
import GroundTheory.HeightsAndTheta.Heights.Regularisation.ProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PBoundedGlue
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Metric
open GroundTheory.Heights₂.Heights (CP)
open GroundTheory.Heights₂.Heights.Regular (RegChartData BoundedPshData)
open GroundTheory.Heights₂.Heights.Regular.ProjectiveLine

def vecL (z : (Σ _ : Unit, Fin 2) → ℂ) : Fin 2 → ℂ := fun i => z ⟨(), i⟩

def projL (z : (Σ _ : Unit, Fin 2) → ℂ) : CP 1 :=
  if h : vecL z ≠ 0 then Projectivization.mk ℂ (vecL z) h else CP.chartInv 0 0

theorem vecL_ne_zero {z : (Σ _ : Unit, Fin 2) → ℂ} (hz : z ∈ mcPts (mCoordIdeal yLine)) : vecL z ≠ 0 := by
  obtain ⟨i, hi⟩ := mem_mcPts_line.1 hz
  exact fun h => hi (congrFun h i)

theorem lineSections (x : CP 1) : ∃ U : Set (CP 1), IsOpen U ∧ x ∈ U ∧ ∃ s : CP 1 → (Σ _ : Unit, Fin 2) → ℂ,
    (∀ y ∈ U, s y ∈ mcPts (mCoordIdeal yLine) ∧ projL (s y) = y) ∧
      ∀ p, cpAtlas.HoloOn U fun y => s y p := by
  refine ⟨CP.chartDomain (CP.chartIndex x), CP.isOpen_chartDomain _, CP.mem_chartDomain_chartIndex x,
    fun y p => CP.chartVec (CP.chartIndex x) (CP.chartCoord (CP.chartIndex x) y) p.2, fun y hy => ?_, fun p => ?_⟩
  · have hne := CP.chartVec_ne_zero (CP.chartIndex x) (CP.chartCoord (CP.chartIndex x) y)
    refine ⟨mem_mcPts_line.2 ⟨CP.chartIndex x, by simp⟩, ?_⟩
    unfold projL
    split_ifs with h
    · exact CP.chartInv_chartCoord _ hy
    · exact absurd hne h
  · intro j w hw
    have hw2 : CP.chartVec j w (CP.chartIndex x) ≠ 0 := hw.2
    exact (analyticAt_chartVec_apply (CP.chartIndex x) p.2 _).comp
      (analyticOnNhd_transition j (CP.chartIndex x) w hw2)

def lineModel : CxModel (mCoordIdeal yLine) 1 where
  Xc := CP 1
  atlas := cpAtlas
  proj := projL
  surj x := by
    induction x using Projectivization.ind with
    | h v hv =>
      refine ⟨fun p => v p.2, ?_, ?_⟩
      · obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
        exact mem_mcPts_line.2 ⟨i, hi⟩
      · unfold projL
        split_ifs with h
        · rfl
        · exact absurd hv h
  fibre z hz z' hz' := by
    unfold projL
    rw [dif_pos (vecL_ne_zero hz), dif_pos (vecL_ne_zero hz'), Projectivization.mk_eq_mk_iff]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨fun _ => (a⁻¹ : ℂˣ), fun _ => Units.ne_zero _, ?_⟩
      funext p
      obtain ⟨⟨⟩, i⟩ := p
      have := congrFun ha i
      simp only [vecL, Pi.smul_apply, Units.smul_def, smul_eq_mul] at this
      simp only [torusSmul]
      rw [← this, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    · rintro ⟨c, hc, rfl⟩
      refine ⟨Units.mk0 (c ())⁻¹ (inv_ne_zero (hc ())), ?_⟩
      funext i
      simp [vecL, torusSmul, Units.smul_mk0, inv_mul_cancel_left₀ (hc ())]
  cont := by
    refine continuousOn_iff_continuous_restrict.2 ?_
    have hc : Continuous fun z : mcPts (mCoordIdeal yLine) =>
        Projectivization.mk' ℂ (⟨vecL z.1, vecL_ne_zero z.2⟩ : {v : Fin 2 → ℂ // v ≠ 0}) :=
      GroundTheory.Heights₂.Heights.ProjTopology.continuous_mk'.comp (Continuous.subtype_mk
        (f := fun z : mcPts (mCoordIdeal yLine) => vecL z.1) (by
          show Continuous fun z : mcPts (mCoordIdeal yLine) => fun i : Fin 2 => z.1 ⟨(), i⟩
          exact continuous_pi fun i => (continuous_apply _).comp continuous_subtype_val) _)
    convert hc using 1
    funext z
    show projL z.1 = _
    unfold projL
    rw [dif_pos (vecL_ne_zero z.2)]
    rfl
  sections := lineSections

def refOne : HermLine (PBlk 2) := HermLine.ofWeight (fun _ => 0) fun _ _ _ => rfl

theorem refOne_h (z : (Σ _ : Unit, Fin 2) → ℂ) : refOne.h z = 1 := by simp [refOne, HermLine.ofWeight]

theorem refOne_smooth : IsSmoothHerm refOne := by
  have : refOne.h = fun _ => 1 := funext refOne_h
  unfold IsSmoothHerm
  rw [this]
  exact contDiffOn_const

variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

theorem th_ref_line (x y : CP 1) : ∃ U : Set (CP 1), IsOpen U ∧ y ∈ U ∧ U ⊆ Set.univ ∧
    ∃ s : CP 1 → (Σ _ : Unit, Fin 2) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (mCoordIdeal yLine) ∧ projL (s y') = y') ∧
      (∀ p, cpAtlas.HoloOn U fun y' => s y' p) ∧ ∃ G : CP 1 → ℂ, cpAtlas.HoloOn U G ∧
        ∀ y' ∈ U, (0 : ℝ) - Real.log (refOne.h (s y')) = (G y').re := by
  obtain ⟨U, hU, hy, s, hs, hh⟩ := lineSections y
  exact ⟨U, hU, hy, Set.subset_univ _, s, hs, hh, fun _ => 0, holoOn_zero' _ _, fun y' _ => by simp [refOne_h]⟩

def lineReg : LogLogRegularisationSetting lineModel (lineData II hII).Xo (muLine (lineHodge II hII)) where
  ref := refOne
  ref_deg := rfl
  ref_smooth := refOne_smooth
  R := cpReg
  th_ref x y _ := th_ref_line x y
  Yo_sub x _ := by
    obtain ⟨z, hz, hzx⟩ := lineModel.surj x
    exact ⟨z, ⟨⟨hz, fun h => absurd h (Set.notMem_empty _)⟩, hz⟩, hzx⟩
  ph_eq z hz _ := by
    show (0 : ℝ) = _
    rw [muLine_h (mem_mcPts_line.1 hz.2), refOne_h, Real.log_one, sub_zero]
  ρ := (ReciprocityTheory.AnForm.A.mollifierInhabit_thm 1).some
  η := cpEta
  Cη := cpCutoff.choose
  cutoff := cpCutoff.choose_spec
  K _ := 0
  e1 t := t
  e1_ge _ _ := le_rfl

def lineBReg : BoundedRegularisationSetting lineModel (lineData II hII).Xo
    (lineHodge II hII).aMu (cuspCorrected (lineHodge II hII) (gaussCusp II hII)) where
  ref := refOne
  ref_deg := rfl
  ref_smooth := refOne_smooth
  B := cpBounded
  th_ref x y _ := th_ref_line x y
  ph_eq z hz := by
    show (0 : ℝ) = _
    rw [cuspCorrected, phMu_line (mem_mcPts_line.1 hz.2), cuspWeight_gauss, refOne_h, Real.log_one]
    ring
  ρ := (ReciprocityTheory.AnForm.A.mollifierInhabit_thm 1).some
  η := cpEta
  Cη := cpCutoff.choose
  cutoff := cpCutoff.choose_spec
  e1 t := t
  e1_ge _ _ := le_rfl

theorem cpBounded_phReg (ρ : ReciprocityTheory.AnForm.A.Mollifier 1) (t : ℝ) (j : Fin cpBounded.N) (x : CP 1) :
    cpBounded.phReg ρ t j x = 0 := by
  simp [BoundedPshData.phReg, BoundedPshData.smoothed, BoundedPshData.u,
    GroundTheory.Heights₂.Heights.Regular.PotentialCharts.chartFun, ReciprocityTheory.AnForm.A.molli, cpBounded, cpCharts]

end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
