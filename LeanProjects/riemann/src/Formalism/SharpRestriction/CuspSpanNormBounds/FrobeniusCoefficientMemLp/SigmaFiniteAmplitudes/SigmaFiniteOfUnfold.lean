import Formalism.HermitianCurvature.HermitianCurvatureProofs.FdegOfSchur
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemma3
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

section General

variable {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace A]

theorem sigmaFinite_of_unfold (M : Measure X) [SigmaFinite M] (ν : Measure Y) (μ : Measure A) [SFinite μ]
    (hμ : μ ≠ 0) (m : Y × A → X) (hm : Measurable m)
    (h : ∀ f : X → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂M = ∫⁻ y, ∫⁻ a, f (m (y, a)) ∂μ ∂ν) :
    SigmaFinite ν := by
  obtain ⟨w, hwpos, hwm, hwi⟩ := exists_pos_lintegral_lt_of_sigmaFinite M (ε := 1) one_ne_zero
  set W : Y → ℝ≥0∞ := fun y => ∫⁻ a, (w (m (y, a)) : ℝ≥0∞) ∂μ with hWdef
  have hWm : Measurable W :=
    Measurable.lintegral_prod_right' ((measurable_coe_nnreal_ennreal.comp hwm).comp hm)
  have hWpos : ∀ y, W y ≠ 0 := by
    intro y hy
    have hm' : Measurable fun a => (w (m (y, a)) : ℝ≥0∞) :=
      (measurable_coe_nnreal_ennreal.comp hwm).comp (hm.comp measurable_prodMk_left)
    rw [hWdef, lintegral_eq_zero_iff hm'] at hy
    have : μ Set.univ = 0 := by
      have h0 : ∀ᵐ a ∂μ, False := by
        filter_upwards [hy] with a ha
        have := hwpos (m (y, a))
        simp only [Pi.zero_apply, ENNReal.coe_eq_zero] at ha
        exact (ne_of_gt this) ha
      simpa using (ae_iff.mp h0)
    exact hμ (Measure.measure_univ_eq_zero.mp this)
  have hWi : ∫⁻ y, W y ∂ν < ⊤ := by
    have h1 := h (fun x => (w x : ℝ≥0∞)) (measurable_coe_nnreal_ennreal.comp hwm)
    calc ∫⁻ y, W y ∂ν = ∫⁻ x, (w x : ℝ≥0∞) ∂M := h1.symm
      _ < ⊤ := hwi.trans ENNReal.one_lt_top
  refine ⟨⟨{ set := fun n : ℕ => {y | ((n : ℝ≥0∞) + 1)⁻¹ ≤ W y}
             set_mem := fun _ => trivial
             finite := fun n => ?_
             spanning := ?_ }⟩⟩
  · have hε : ((n : ℝ≥0∞) + 1)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (by simp)
    have hε' : ((n : ℝ≥0∞) + 1)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (by simp)
    calc ν {y | ((n : ℝ≥0∞) + 1)⁻¹ ≤ W y} ≤ (∫⁻ y, W y ∂ν) / ((n : ℝ≥0∞) + 1)⁻¹ :=
          meas_ge_le_lintegral_div hWm.aemeasurable hε hε'
      _ < ⊤ := ENNReal.div_lt_top hWi.ne hε
  · refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (hWpos y)
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    show ((n : ℝ≥0∞) + 1)⁻¹ ≤ W y
    refine le_trans ?_ hn.le
    exact ENNReal.inv_le_inv.mpr le_self_add

theorem map_of_unfold (M : Measure X) (ν : Measure Y) (μ : Measure A) [SFinite μ]
    (m : Y × A → X) (hm : Measurable m)
    (h : ∀ f : X → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂M = ∫⁻ y, ∫⁻ a, f (m (y, a)) ∂μ ∂ν) :
    M = (ν.prod μ).map m := by
  ext s hs
  rw [Measure.map_apply hm hs, Measure.prod_apply (hm hs)]
  have h1 := h (s.indicator 1) (measurable_one.indicator hs)
  rw [lintegral_indicator_one hs] at h1
  rw [h1]
  refine lintegral_congr fun y => ?_
  rw [← lintegral_indicator_one (measurable_prodMk_left (hm hs))]
  rfl

end General

section Local

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

theorem mp_inv_W_sk {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) {μ : Measure (Mt k r)}
    (h : Formalism.MainNotions.S.IsHaarOn (UWset k r z) μ) :
    MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μ μ :=
  Formalism.FourierDecayAlt.P.S3dx6.measurePreserving_invM_of_isHaarOn (Formalism.MainNotions.BridgeLemma₃.hu_haarUp.1 k r z μ hz hT h)

theorem map_inv_haarLieN (κ : ℝ≥0∞) :
    (haarLie (Nset k r) κ).map (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) = haarLie (Nset k r) κ := by
  obtain ⟨c, -, he⟩ := Formalism.MainNotions.BridgeCSB.haarLie_N_eq (k := k) (r := r)
  have h0 := (Formalism.FourierDecayAlt.P.S3dx6.mp_inv_N
    (Formalism.MainNotions.BridgeLemma₃.hu_haarUp.2 k r _ Formalism.MainNotions.BridgeCSB.isHaarOn_nuN)).map_eq
  rw [he κ, Measure.map_smul, Measure.map_smul, h0]

theorem ae_mem_sk {S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)} {μ : Measure (Mt k r)} (h : Formalism.MainNotions.S.IsHaarOn S μ) :
    ∀ᵐ x ∂μ, Matrix.of x ∈ S := by
  rw [ae_iff]
  simpa using h.2.2.1

theorem ae_mem_haarLieN (κ : ℝ≥0∞) : ∀ᵐ x ∂(haarLie (Nset k r) κ), Matrix.of x ∈ Nset k r := by
  rw [ae_iff]
  simpa using Formalism.MainNotions.LowestKTypeMultiplicity.muN_conc (k := k) (r := r) κ

end Local

end Formalism.MainNotions.S.Pv.AmpDDPf
