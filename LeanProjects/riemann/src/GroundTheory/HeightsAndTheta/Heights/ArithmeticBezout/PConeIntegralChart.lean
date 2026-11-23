import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeChartArea
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeChartIntegrable
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFsLogSmul
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsSheet sheetDensity ptsIntegralAt pot)

theorem hermLine_h_eq {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S)
    (z : (Σ _ : Unit, PBlk n ()) → ℂ) :
    (IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS).h z = ‖WithLp.toLp 2 (S *ᵥ fun i => z ⟨(), i⟩)‖ := by
  simp [IndefiniteRowSideFullHecke.ArithBezout.hermLine, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics,
    IndefiniteRowSideFullHecke.ArithBezout.pointMetric]

theorem measurable_fsLog {n : ℕ} (h : HermNorm n) (u : Fin n → ℂ) : Measurable (fsLog h u) := by
  unfold fsLog HermNorm.dualNorm
  simp only [Matrix.mulVec, dotProduct]
  exact Real.measurable_log.comp (Measurable.div (Continuous.measurable (by fun_prop))
    (Continuous.measurable (by fun_prop)))

theorem ConeIntegralChart.proof (hA : ConeChartArea.Statement) (hB : ChartGramMA.Statement)
    (hI : ConeChartIntegrable.Statement) : ConeIntegralChart.Statement := by
  intro n e S hS P u Ψ hP hu hΨ
  rw [hA n e S hS P Ψ _ hP hΨ (measurable_fsLog _ u)
    (fun c z hc => FsLogSmul.proof n _ u z c hc) (hI n e _ P u hP hu)]
  unfold ptsIntegralAt
  congr 1
  funext y
  refine finsum_mem_congr rfl fun w _ => ?_
  unfold chartGramDensity sheetDensity
  by_cases hγ : ∃ γ, IsSheet P Ψ y w γ
  · simp only [dif_pos hγ]
    have hev := hγ.choose_spec.2
    have hg : fsLog (ObjectsHeight.ofPointMatrix S hS) u (fun i => hγ.choose y ⟨(), i⟩) =
        IndefiniteRowSideFullHecke.ArithBezout.logFormNorm S hS u (hγ.choose y) := by
      rw [ObjectsHeight.ofPointMatrix_fsLog]
    have hpot : (fun (j : Fin e) y' =>
        pot (fun _ : Fin e => IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS) j (hγ.choose y')) =
        fun _ y' => Real.log ‖WithLp.toLp 2 (S *ᵥ fun i => hγ.choose y' ⟨(), i⟩)‖ := by
      funext j y'
      simp only [pot, hermLine_h_eq]
    rw [hg, hpot, hB e n _ y ?_ ?_]
    · filter_upwards [hev] with y' hy'
      refine differentiableAt_pi.2 fun i => ?_
      simp only [Matrix.mulVec, dotProduct]
      exact DifferentiableAt.fun_sum fun j _ => (differentiableAt_pi.1 hy'.1 ⟨(), j⟩).const_mul _
    · obtain ⟨i, hi⟩ := hev.self_of_nhds.2.1.1 ()
      intro h0
      have h1 := Matrix.mulVec_injective_iff_isUnit.mpr hS (h0.trans (Matrix.mulVec_zero S).symm)
      exact hi (congrFun h1 i)
  · simp only [dif_neg hγ]

end GroundTheory.Heights₂.Heights
