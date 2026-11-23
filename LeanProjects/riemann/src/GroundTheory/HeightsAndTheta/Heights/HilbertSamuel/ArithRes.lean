import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.KerEqBotOfCoord
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffOnFubiniStudyProfileInvNormSqFirst
import GroundTheory.HeightsAndTheta.Heights.FubiniStudy
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyTransition
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyMetric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory
open scoped ComplexConjugate

noncomputable section

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

structure AnRes (P J : Ideal (MRing ι)) (e : ℕ) where

  homog : IsMultiHomogIdeal J

  nondeg : ¬ J ≤ P

  X : Type
  [top : TopologicalSpace X]
  [compact : CompactSpace X]
  [t2 : T2Space X]

  A : FinHolAtlas e X

  U : X → Set X
  isOpen_U : ∀ x, IsOpen (U x)
  mem_U : ∀ x, x ∈ U x

  lift : X → X → (Σ k, ι k) → ℂ
  holo : ∀ x p, A.HoloOn (U x) (fun y => lift x y p)
  mem : ∀ x, ∀ y ∈ U x, lift x y ∈ mcPts P

  compat : ∀ x x', ∀ y ∈ U x ∩ U x', SameOrbit (lift x y) (lift x' y)

  surj : ∀ z ∈ mcPts P, z ∉ mcPts J → ∃ x, SameOrbit (lift x x) z

  inj : ∀ x x', lift x x ∉ mcPts J → SameOrbit (lift x x) (lift x' x') → x = x'

  null : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' {x | lift x x ∈ mcPts J}) = 0

attribute [instance] AnRes.top AnRes.compact AnRes.t2

def _root_.ReciprocityTheory.ChartRestriction.G.Geo.AnLogRes.toAnRes {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) :
    AnRes P J e where
  homog := R.homog
  nondeg := R.nondeg
  X := R.X
  A := R.A
  U := R.U
  isOpen_U := R.isOpen_U
  mem_U := R.mem_U
  lift := R.lift
  holo := R.holo
  mem := R.mem
  compat := R.compat
  surj := R.surj
  inj := R.inj
  null := R.null

def IsSmoothVolume {e : ℕ} {X : Type*} [TopologicalSpace X] [MeasurableSpace X] (A : FinHolAtlas e X)
    (dV : Measure X) : Prop :=
  IsProbabilityMeasure dV ∧ ∀ j, ∃ ν : (Fin e → ℂ) → ℝ,
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν (A.chart j).target ∧ (∀ y ∈ (A.chart j).target, 0 < ν y) ∧
    ∀ S : Set X, MeasurableSet S → S ⊆ (A.chart j).source →
      dV S = ∫⁻ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' S, ENNReal.ofReal (ν y)

structure HSMDatum (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] where

  x : Ix κ → Ω

  m : ConeMetric ℂ (Ix κ)

  P0 : Ideal (MRing (GlobalTheory κ))

  J : Ideal (MRing (GlobalTheory κ))

  R : AnRes (ι := GlobalTheory κ) (coordIdeal ℤ x) J D
  [meas : MeasurableSpace R.X]
  [borel : BorelSpace R.X]

  dV : Measure R.X
  one_le : 1 ≤ D
  arith : IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1)
  indep : LinearIndependent ℤ x
  smooth : IsSmoothMetric m
  conjInv : IsConjInvariant m
  normalForm_baseLattice_le_dualSpan_sup_line : P0 ≤ coordIdeal ℤ x
  semipos : IsSemipositiveRel P0 (coordIdeal ℤ x) (HermLine.ofCone m)
  vol : IsSmoothVolume R.A dV

attribute [instance] HSMDatum.meas HSMDatum.borel

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def resPt (d : HSMDatum D Ω κ) (y : d.R.X) : Ix κ → ℂ := d.R.lift y y

def pairVal (m : ConeMetric ℂ (Ix κ)) (n : ℕ) (b b' : MvPolynomial (Ix κ) ℚ) (z : Ix κ → ℂ) : ℂ :=
  eval z (map (algebraMap ℚ ℂ) b) * conj (eval z (map (algebraMap ℚ ℂ) b')) / ((m.ρ z ^ (2 * n) : ℝ) : ℂ)

def resGram (d : HSMDatum D Ω κ) (n : ℕ) {r : ℕ} (b : Fin r → MvPolynomial (Ix κ) ℚ) :
    Matrix (Fin r) (Fin r) ℝ :=
  fun k l => (1 / 2) * ((∫ y, pairVal d.m n (b k) (b l) (resPt d y) ∂d.dV).re +
    (∫ y, pairVal d.m n (b k) (b l) (conjPt (resPt d y)) ∂d.dV).re)

open Classical in

def resChi (d : HSMDatum D Ω κ) (n : ℕ) : ℝ :=
  if h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n p.2 then
    -(1 / 2) * Real.log (resGram d n h.choose.2).det
  else 0

def resolutionSectionL2Norm (d : HSMDatum D Ω κ) (n : ℕ) (f : MvPolynomial (Ix κ) ℤ) : ℝ :=
  Real.sqrt ((1 / 2) * ((∫ y, ptNorm d.m (Int.castRingHom ℂ) n f (resPt d y) ^ 2 ∂d.dV) +
    ∫ y, ptNorm d.m (Int.castRingHom ℂ) n f (conjPt (resPt d y)) ^ 2 ∂d.dV))

namespace ProjLine

def projectiveLineAnalyticResolution : AnRes (ι := GlobalTheory (Fin 2)) (coordIdeal ℤ y) ProjectiveLineResolution.JJ 1 where
  homog := ProjectiveLineResolution.res.homog
  nondeg := by rw [coordIdeal_y]; exact ProjectiveLineResolution.res.nondeg
  X := OnePoint ℂ
  A := p1
  U := ProjectiveLineResolution.res.U
  isOpen_U := ProjectiveLineResolution.res.isOpen_U
  mem_U := ProjectiveLineResolution.res.mem_U
  lift := ProjectiveLineResolution.res.lift
  holo := ProjectiveLineResolution.res.holo
  mem := by rw [coordIdeal_y]; exact ProjectiveLineResolution.res.mem
  compat := ProjectiveLineResolution.res.compat
  surj := by rw [coordIdeal_y]; exact ProjectiveLineResolution.res.surj
  inj := ProjectiveLineResolution.res.inj
  null := ProjectiveLineResolution.res.null

def projectiveLineMeasurableSpace : MeasurableSpace (OnePoint ℂ) := borel (OnePoint ℂ)

attribute [local instance] projectiveLineMeasurableSpace

instance projectiveLineBorel : BorelSpace (OnePoint ℂ) := ⟨rfl⟩

theorem measurable_p1Chart0_symm : Measurable projectiveLineChartAtZero.symm :=
  (OnePoint.continuous_coe.comp (continuous_apply 0)).measurable

def fubiniStudyVolumeProjectiveLine : Measure (OnePoint ℂ) := (GroundTheory.Heights₂.Heights.CP.fsChartMeasure (N := 1) 0).map projectiveLineChartAtZero.symm

theorem contDiff_fsVolumeDensity (i : Fin 2) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (GroundTheory.Heights₂.Heights.CP.fsVolumeDensity (N := 1) i) := by
  have h : GroundTheory.Heights₂.Heights.CP.fsVolumeDensity (N := 1) i =
      fun z => (Nat.factorial 1 : ℝ) / (Real.pi ^ 1 * (1 + GroundTheory.Heights₂.Heights.normSqSum z) ^ (1 + 1)) := by
    funext z
    exact GroundTheory.Heights₂.Heights.CP.fsVolumeDensity_eq i z
  rw [h]
  refine contDiff_const.div (contDiff_const.mul ((contDiff_const.add ?_).pow _)) fun z => ?_
  · exact GroundTheory.Heights₂.Heights.CP.contDiff_normSqSum
  · have := GroundTheory.Heights₂.Heights.one_add_normSqSum_pos z
    have := Real.pi_pos
    positivity

theorem transition_apply_one_zero (v : Fin 1 → ℂ) :
    GroundTheory.Heights₂.Heights.CP.transition (N := 1) 1 0 v = fun _ => (v 0)⁻¹ := by
  funext k
  obtain rfl : k = 0 := Subsingleton.elim _ _
  rw [GroundTheory.Heights₂.Heights.CP.transition_apply]
  simp [GroundTheory.Heights₂.Heights.CP.chartVec, Fin.insertNth]
  first
  | rfl
  | simp [Fin.succAboveCases]

theorem chartVec_one_zero' (v : Fin 1 → ℂ) : GroundTheory.Heights₂.Heights.CP.chartVec (N := 1) 1 v 0 = v 0 := by
  simp [GroundTheory.Heights₂.Heights.CP.chartVec, Fin.insertNth]
  first
  | rfl
  | simp [Fin.succAboveCases]

theorem fubiniStudyVolume_projectiveLine_apply {S : Set (OnePoint ℂ)} (hS : MeasurableSet S) :
    fubiniStudyVolumeProjectiveLine S = ∫⁻ w in projectiveLineChartAtZero.symm ⁻¹' S,
      ENNReal.ofReal (GroundTheory.Heights₂.Heights.CP.fsVolumeDensity (N := 1) 0 w) := by
  rw [fubiniStudyVolumeProjectiveLine, Measure.map_apply measurable_p1Chart0_symm hS, GroundTheory.Heights₂.Heights.CP.fsChartMeasure,
    withDensity_apply _ (measurable_p1Chart0_symm hS)]

theorem projectiveLineSecondChart_symm_eq (v : Fin 1 → ℂ) (hv : v 0 ≠ 0) : projectiveLineChartAtInfinity.symm v = (((v 0)⁻¹ : ℂ) : OnePoint ℂ) := by
  show projectiveLineChartAtInfinity.invFun v = _
  simp only [projectiveLineChartAtInfinity, hv, if_false]

theorem isSmoothVolume_p1Vol : IsSmoothVolume p1 fubiniStudyVolumeProjectiveLine := by
  refine ⟨⟨?_⟩, fun j => ?_⟩
  · rw [fubiniStudyVolume_projectiveLine_apply MeasurableSet.univ, Set.preimage_univ, Measure.restrict_univ]
    exact GroundTheory.Heights₂.Heights.CP.lintegral_fsVolumeDensity 0
  · fin_cases j
    · refine ⟨GroundTheory.Heights₂.Heights.CP.fsVolumeDensity (N := 1) 0, (contDiff_fsVolumeDensity 0).contDiffOn,
        fun y _ => GroundTheory.Heights₂.Heights.CP.fsVolumeDensity_pos 0 y, fun S hS _ => ?_⟩
      change _ = ∫⁻ y in projectiveLineChartAtZero.target ∩ projectiveLineChartAtZero.symm ⁻¹' S, _
      rw [projLineChart0_target, Set.univ_inter, fubiniStudyVolume_projectiveLine_apply hS]
    · refine ⟨GroundTheory.Heights₂.Heights.CP.fsVolumeDensity (N := 1) 1, (contDiff_fsVolumeDensity 1).contDiffOn,
        fun y _ => GroundTheory.Heights₂.Heights.CP.fsVolumeDensity_pos 1 y, fun S hS hsub => ?_⟩
      change _ = ∫⁻ y in projectiveLineChartAtInfinity.target ∩ projectiveLineChartAtInfinity.symm ⁻¹' S, _
      have hsub' : S ⊆ {x | x ≠ ((0 : ℂ) : OnePoint ℂ)} := hsub
      rw [projLineChart1_target, Set.univ_inter, fubiniStudyVolume_projectiveLine_apply hS]
      set T := GroundTheory.Heights₂.Heights.CP.transition (N := 1) 1 0 with hT
      set A := projectiveLineChartAtInfinity.symm ⁻¹' S with hAdef
      set A' := A ∩ {v : Fin 1 → ℂ | v 0 ≠ 0} with hA'def
      have hA : MeasurableSet A := continuous_chart1_inv.measurable hS
      have hA' : MeasurableSet A' :=
        hA.inter (isOpen_ne_fun (continuous_apply 0) continuous_const).measurableSet
      have hTv : ∀ v : Fin 1 → ℂ, T v = fun _ => (v 0)⁻¹ := transition_apply_one_zero
      have himg : T '' A' = projectiveLineChartAtZero.symm ⁻¹' S := by
        ext w
        constructor
        · rintro ⟨v, ⟨hvA, hv0⟩, rfl⟩
          change projectiveLineChartAtZero.symm (T v) ∈ S
          rw [projLineChart0_symm_apply, hTv]
          have := hvA
          rw [Set.mem_preimage, projectiveLineSecondChart_symm_eq v hv0] at this
          exact this
        · intro hw
          rw [Set.mem_preimage, projLineChart0_symm_apply] at hw
          have hw0 : w 0 ≠ 0 := fun h => hsub' hw (by rw [h])
          refine ⟨fun _ => (w 0)⁻¹, ⟨?_, inv_ne_zero hw0⟩, ?_⟩
          · rw [Set.mem_preimage, projectiveLineSecondChart_symm_eq _ (inv_ne_zero hw0), inv_inv]
            exact hw
          · rw [hTv]
            funext k
            obtain rfl : k = 0 := Subsingleton.elim _ _
            simp
      have hderiv : ∀ v ∈ A', HasFDerivWithinAt T (fderiv ℝ T v) A' v := by
        intro v hv
        have hz : GroundTheory.Heights₂.Heights.CP.chartVec (N := 1) 1 v 0 ≠ 0 := by
          rw [chartVec_one_zero']
          exact hv.2
        exact (((GroundTheory.Heights₂.Heights.CP.differentiableAt_transition 1 0 hz).restrictScalars ℝ).hasFDerivAt).hasFDerivWithinAt
      have hinj : Set.InjOn T A' := by
        intro v hv v' hv' h
        rw [hTv, hTv] at h
        have h0 := congrFun h 0
        simp only [inv_inj] at h0
        funext k
        obtain rfl : k = 0 := Subsingleton.elim _ _
        exact h0
      rw [← himg, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA' hderiv hinj]
      have hae : A =ᵐ[volume] A' := by
        refine (ae_eq_set.mpr ⟨?_, ?_⟩).symm
        · rw [Set.sdiff_eq_empty.mpr Set.inter_subset_left]
          exact measure_empty
        · refine measure_mono_null (t := {0}) ?_ (measure_singleton 0)
          rintro v ⟨hvA, hv⟩
          rw [Set.mem_singleton_iff]
          funext k
          obtain rfl : k = 0 := Subsingleton.elim _ _
          by_contra h
          exact hv ⟨hvA, h⟩
      rw [setLIntegral_congr hae]
      refine setLIntegral_congr_fun hA' fun v hv => ?_
      have hz : GroundTheory.Heights₂.Heights.CP.chartVec (N := 1) 1 v 0 ≠ 0 := by
        rw [chartVec_one_zero']
        exact hv.2
      rw [← ENNReal.ofReal_mul (abs_nonneg _),
        ← GroundTheory.Heights₂.Heights.CP.fsVolumeDensity_transition 1 0 hz]

def hsmProjLine : HSMDatum 1 FnField (Fin 2) where
  x := y
  m := fsMetric (Ix (Fin 2))
  P0 := ⊥
  J := ProjectiveLineResolution.JJ
  R := projectiveLineAnalyticResolution
  meas := projectiveLineMeasurableSpace
  borel := projectiveLineBorel
  dV := fubiniStudyVolumeProjectiveLine
  one_le := le_rfl
  arith := isArithVar_y
  indep := linearIndependent_y
  smooth := isSmoothMetric_fs
  conjInv := isConjInvariant_fs
  normalForm_baseLattice_le_dualSpan_sup_line := bot_le
  semipos := isSemipositiveRel_fs _ _
  vol := isSmoothVolume_p1Vol

end ProjLine

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
