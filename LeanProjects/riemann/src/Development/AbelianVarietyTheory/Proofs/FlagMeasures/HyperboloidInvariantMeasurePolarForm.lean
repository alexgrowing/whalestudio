import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvO
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ConstPair
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsTest
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.TransW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.PolarHyp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushCut
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushH
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushM
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushI
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushC

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace GlobalTheory.HyperboloidPolar

open PI.RhsWLim PI.RhsWLim.W

variable {k r : ℕ}

theorem opVec_inWb (p : (Fin k → ℂ) × ℂ) : inWb k r (opVec k r p) := by
  intro i hi
  unfold opVec
  rw [dif_neg (by omega), if_neg (by omega)]

theorem wbPart_opVec (p : (Fin k → ℂ) × ℂ) : wbPart k r (opVec k r p) = toW k p := by
  funext m
  have := m.isLt
  unfold wbPart opVec toW wI
  by_cases h : m.val < k
  · rw [dif_pos (by simp only; omega), dif_pos h]
    exact congrArg p.1 (Fin.ext (by simp))
  · rw [dif_neg (by simp only; omega), dif_neg h, if_pos (by simp only; omega)]

theorem opCo_eq (v : Fin (2 * r + k + 1) → ℂ) : opCo k r v = ofW k (wbPart k r v) := rfl

theorem opCo_opVec (p : (Fin k → ℂ) × ℂ) : opCo k r (opVec k r p) = p := by
  rw [opCo_eq, wbPart_opVec, ofW_toW]

theorem eq_of_wbPart {v w : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (hw : inWb k r w)
    (h : wbPart k r v = wbPart k r w) : v = w := by
  funext i
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [hv i hi, hw i hi]
  · have hm : MB.mid k r i := by constructor <;> omega
    have := congrFun h (MB.midx hm)
    simpa only [wbPart, MB.wI_midx] using this

theorem opVec_opCo {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) : opVec k r (opCo k r v) = v :=
  eq_of_wbPart (opVec_inWb _) hv (by rw [wbPart_opVec, opCo_eq, toW_ofW])

theorem inWb_uwb {s : Mat k r} (hs : s ∈ UWb k r) {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    inWb k r (s *ᵥ v) := by
  rw [op_uwb_eq_emb hs]
  exact RI.inWb_emb _ hv

theorem continuous_opVec : Continuous (opVec k r) := by
  refine continuous_pi fun i => ?_
  unfold opVec
  by_cases h : r ≤ i.val ∧ i.val < r + k
  · simp only [dif_pos h]
    exact (continuous_apply _).comp continuous_fst
  · simp only [dif_neg h]
    by_cases h' : i.val = r + k
    · simp only [if_pos h']
      exact continuous_snd
    · simp only [if_neg h']
      exact continuous_const

theorem continuous_opCo : Continuous (opCo k r) :=
  (continuous_pi fun i => continuous_apply (wI k r (Fin.castSucc i))).prodMk
    (continuous_apply (wI k r (Fin.last k)))

theorem herm_opVec (p : (Fin k → ℂ) × ℂ) :
    herm (Hpk k r) (opVec k r p) (opVec k r p) = (qf k p : ℂ) := by
  rw [herm_wb _ _ (opVec_inWb p), wbPart_opVec, qf_eq]
  rfl

theorem herm_self_eq {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    herm (Hpk k r) z z = ((-Tz k r z : ℝ) : ℂ) := by
  unfold Tz
  rw [neg_neg, herm_wb _ _ hz, hermHb_self, Complex.ofReal_re]

def hypAmb (k r : ℕ) (T' : ℝ) : Measure (Fin (2 * r + k + 1) → ℂ) := (hypM k T').map (opVec k r)

theorem hypAmb_sigmaFinite {T' : ℝ} (hT' : 0 < T') : SigmaFinite (hypAmb k r T') := by
  have : IsFiniteMeasureOnCompacts (hypAmb k r T') := by
    refine ⟨fun C hC => ?_⟩
    rw [hypAmb, Measure.map_apply continuous_opVec.measurable hC.measurableSet]
    refine lt_of_le_of_lt (measure_mono ?_) ((hypLF k T' hT').2 _ (hC.image continuous_opCo))
    intro p hp
    exact ⟨_, hp, opCo_opVec p⟩
  infer_instance

theorem hypAmb_inv (hk : 1 ≤ k) {T' : ℝ} (hT' : 0 < T') {s : Mat k r} (hs : s ∈ UWb k r) :
    (hypAmb k r T').map (fun v => s *ᵥ v) = hypAmb k r T' := by
  have hI := hypInv_of lebInvB (coneForm_of hypTh coneVol) k r T' hk hT' s hs
  have hm : Continuous (fun v : Fin (2 * r + k + 1) → ℂ => s *ᵥ v) :=
    continuous_const.matrix_mulVec continuous_id
  have hA : Continuous (opAct k r s) := continuous_opCo.comp (hm.comp continuous_opVec)
  have e : (fun v => s *ᵥ v) ∘ opVec k r = opVec k r ∘ opAct k r s := by
    funext p
    exact (opVec_opCo (inWb_uwb hs (opVec_inWb p))).symm
  rw [hypAmb, Measure.map_map hm.measurable continuous_opVec.measurable, e,
    ← Measure.map_map continuous_opVec.measurable hA.measurable, hI]

theorem hypAmb_conc {z' : Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z') (hT' : 0 < Tz k r z') :
    hypAmb k r (Tz k r z') {v | ¬ (inWb k r v ∧ herm (Hpk k r) v v = herm (Hpk k r) z' z')} = 0 := by
  have hc : IsClosed {v : Fin (2 * r + k + 1) → ℂ |
      inWb k r v ∧ herm (Hpk k r) v v = herm (Hpk k r) z' z'} := by
    refine IsClosed.inter ?_ (isClosed_eq ?_ continuous_const)
    · have : {v : Fin (2 * r + k + 1) → ℂ | inWb k r v} =
          ⋂ i : Fin (2 * r + k + 1), ⋂ _ : (i.val < r ∨ r + k < i.val), {v | v i = 0} := by
        ext v
        simp only [inWb, Set.mem_iInter]
        rfl
      show IsClosed {v : Fin (2 * r + k + 1) → ℂ | inWb k r v}
      rw [this]
      exact isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_eq (continuous_apply i) continuous_const
    · unfold herm
      exact continuous_id.star.dotProduct (continuous_const.matrix_mulVec continuous_id)
  have hm : MeasurableSet {v : Fin (2 * r + k + 1) → ℂ |
      ¬ (inWb k r v ∧ herm (Hpk k r) v v = herm (Hpk k r) z' z')} := hc.measurableSet.compl
  rw [hypAmb, Measure.map_apply continuous_opVec.measurable hm]
  refine measure_mono_null ?_ (hypLF k _ hT').1
  intro p hp hS
  apply hp
  refine ⟨opVec_inWb p, ?_⟩
  rw [herm_opVec, herm_self_eq hz', (hypS_iff _ p).1 hS]

theorem hypAmb_polar (hk : 1 ≤ k) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {T' : ℝ} (hT' : 0 < T') (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ v, g (herm (Hpk k r) v z) ∂hypAmb k r T' =
      ENNReal.ofReal (2 * Real.pi ^ k / (k - 1).factorial / (2 * Tz k r z ^ k)) *
        ∫⁻ ζ, ENNReal.ofReal (zWeight k (Tz k r z) T' ζ) * g ζ := by
  obtain ⟨p, hp, hpz⟩ := transW k r z hz hT
  set s := Real.sqrt (Tz k r z) with hs
  have hs0 : (s : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact (Real.sqrt_pos.2 hT).ne'
  set zs := ((s : ℂ) • wLast k r) with hzs
  have hgm : Measurable fun v => g (herm (Hpk k r) v zs) := hg.comp (RI.cont_herm zs).measurable
  have hm : Measurable (fun v : Fin (2 * r + k + 1) → ℂ => p⁻¹ *ᵥ v) :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have step1 : ∫⁻ v, g (herm (Hpk k r) v z) ∂hypAmb k r T' = ∫⁻ v, g (herm (Hpk k r) v zs) ∂hypAmb k r T' := by
    calc ∫⁻ v, g (herm (Hpk k r) v z) ∂hypAmb k r T'
        = ∫⁻ v, (fun y => g (herm (Hpk k r) y zs)) (p⁻¹ *ᵥ v) ∂hypAmb k r T' := by
          refine lintegral_congr fun v => ?_
          rw [← hpz, herm_mulVec_right hp.1]
      _ = ∫⁻ y, g (herm (Hpk k r) y zs) ∂((hypAmb k r T').map (fun v => p⁻¹ *ᵥ v)) :=
          (lintegral_map hgm hm).symm
      _ = _ := by rw [hypAmb_inv hk hT' (HU.uwb_inv hp)]
  set f : (Fin k → ℂ) × ℂ → ℝ≥0∞ := fun v => g (-((s : ℂ) * v.2)) with hf
  have hfm : Measurable f := hg.comp (continuous_const.mul continuous_snd).neg.measurable
  have step2 : ∫⁻ v, g (herm (Hpk k r) v zs) ∂hypAmb k r T' = hypMeas k T' f := by
    rw [hypMeas_eq k T' hfm, hypAmb, lintegral_map hgm continuous_opVec.measurable]
    refine lintegral_congr fun q => ?_
    have e : opVec k r q (wI k r (Fin.last k)) = q.2 := congrArg Prod.snd (opCo_opVec (r := r) q)
    rw [hzs, herm_wLast, e]
  set G : ℝ → ℂ → ℝ≥0∞ := fun _ c => g (-((s : ℂ) * c)) with hGdef
  have hGm : Measurable (Function.uncurry G) :=
    hg.comp (continuous_const.mul continuous_snd).neg.measurable
  have step3 := polarHyp k (Tz k r z) T' hk hT hT' G hGm
  rw [← hs] at step3
  have hcancel : ∀ ζ : ℂ, -((s : ℂ) * -(ζ / (s : ℂ))) = ζ := by
    intro ζ; field_simp
  have e3 : hypMeas k T' f =
      hypMeas k T' (fun v => G ‖(WithLp.equiv 2 (Fin k → ℂ)).symm v.1‖ v.2) := rfl
  rw [step1, step2, e3, step3]
  simp only [hGdef, hcancel]

theorem hypQ : RI.HypQ := by
  intro k r z z' hk hz hz' hT hT'
  refine ⟨hypAmb k r (Tz k r z'), hypAmb_sigmaFinite hT', fun s hs => hypAmb_inv hk hT' hs,
    hypAmb_conc hz' hT', ENNReal.ofReal (2 * Real.pi ^ k / (k - 1).factorial / (2 * Tz k r z ^ k)),
    ?_, ENNReal.ofReal_ne_top, fun g hg => hypAmb_polar hk hz hT hT' g hg⟩
  have := Real.pi_pos
  exact (ENNReal.ofReal_pos.2 (by positivity)).ne'

end GlobalTheory.HyperboloidPolar
