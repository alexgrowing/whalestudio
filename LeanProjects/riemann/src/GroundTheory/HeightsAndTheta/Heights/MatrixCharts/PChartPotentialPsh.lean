import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsPsh
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PshMean
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Metric Real MCPsh

noncomputable section

theorem splitCoord_add_smul (n m : ℕ) (z w : Fin (n + m) → ℂ) (ζ : ℂ) :
    splitCoord n m (z + ζ • w) = splitCoord n m z + ζ • splitCoord n m w := by
  ext <;> simp [splitCoord]

theorem continuous_splitCoord (n m : ℕ) : Continuous (splitCoord n m) :=
  Continuous.prodMk (continuous_pi fun _ => continuous_apply _)
    (continuous_pi fun _ => continuous_apply _)

theorem PeriodChartData.Y_posDef (D : PeriodChartData) {z : Fin D.n → ℂ} (hz : z ∈ D.Ustar) :
    (D.Y z).PosDef := by
  have h := Matrix.PosDef.posSemidef_add (D.Y_ge z hz) (PosDef.one.smul D.c_pos)
  simpa [PeriodChartData.Y] using h

theorem ChartPotentialPsh.proof (hcont : LogDetGramContinuous.Statement)
    (hsub : LogDetGramSubmean.Statement) (hYc : ChartImagContinuous.Statement)
    (hmean : ChartImagMean.Statement) : ChartPotentialPsh.Statement := by
  intro D
  set S := splitCoord D.n D.m ⁻¹' (D.Ustar ×ˢ D.V) with hS
  have hUs : ∀ x ∈ S, splitCoord D.n D.m x ∈ D.U ×ˢ D.V := fun x hx => ⟨hx.1.1, hx.2⟩
  have hYS : ContinuousOn (fun x => D.Y (splitCoord D.n D.m x).1) S :=
    (hYc D).comp (continuous_fst.comp (continuous_splitCoord _ _)).continuousOn
      (fun x hx => hx.1)
  have hFS : ContinuousOn (fun x => D.f (splitCoord D.n D.m x)) S :=
    continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun k =>
      (D.f_analytic j k).continuousOn.comp (continuous_splitCoord _ _).continuousOn hUs
  have hc := hcont (Fin (D.n + D.m) → ℂ) S D.g D.rk (fun x => D.Y (splitCoord D.n D.m x).1)
    (fun x => D.f (splitCoord D.n D.m x)) hYS hFS (fun x hx => D.Y_posDef hx.1)
    (fun x hx => D.f_rank _ (hUs x hx))
  refine ⟨hc.upperSemicontinuousOn, ?_⟩
  intro z w hdisc
  set z' := splitCoord D.n D.m z
  set w' := splitCoord D.n D.m w
  have hline : ∀ ζ ∈ closedBall (0:ℂ) 1, z' + ζ • w' ∈ D.Ustar ×ˢ D.V := fun ζ hζ => by
    have := hdisc ζ (by simpa using hζ)
    rwa [Set.mem_preimage, splitCoord_add_smul] at this
  have hline1 : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z'.1 + ζ • w'.1 ∈ D.Ustar := fun ζ hζ =>
    (hline ζ (by simpa using hζ)).1
  have haff : ∀ ζ : ℂ, AnalyticAt ℂ (fun ζ : ℂ => z' + ζ • w') ζ := fun ζ =>
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hf : ∀ j k, AnalyticOnNhd ℂ (fun ζ : ℂ => D.f (z' + ζ • w') j k) (closedBall 0 1) :=
    fun j k ζ hζ => AnalyticAt.comp (g := fun p => D.f p j k) (f := fun ζ : ℂ => z' + ζ • w')
      (D.f_analytic j k _ ⟨(hline ζ hζ).1.1, (hline ζ hζ).2⟩) (haff ζ)
  have hYd : ContinuousOn (fun ζ : ℂ => D.Y (z'.1 + ζ • w'.1)) (closedBall 0 1) :=
    (hYc D).comp ((continuous_const.add (continuous_id.smul continuous_const)).continuousOn)
      (fun ζ hζ => (hline ζ hζ).1)
  have hm : ∀ j k, circleAverage (fun ζ : ℂ => D.Y (z'.1 + ζ • w'.1) j k) 0 1 =
      D.Y (z'.1 + (0:ℂ) • w'.1) j k := fun j k => by
    rw [zero_smul, add_zero]; exact hmean D z'.1 w'.1 hline1 j k
  obtain ⟨hint, hle⟩ := hsub D.g D.rk (fun ζ => D.Y (z'.1 + ζ • w'.1))
    (fun ζ => D.f (z' + ζ • w')) (fun ζ hζ => D.Y_posDef (hline ζ hζ).1) hYd hm hf
    (fun ζ hζ => D.f_rank _ ⟨(hline ζ hζ).1.1, (hline ζ hζ).2⟩)
  have hfun : (fun ζ : ℂ => (D.u ∘ splitCoord D.n D.m) (z + ζ • w)) =
      fun ζ => logDetGram (D.Y (z'.1 + ζ • w'.1)) (D.f (z' + ζ • w')) := by
    funext ζ
    simp only [Function.comp_apply, PeriodChartData.u, splitCoord_add_smul, z', w',
      Prod.fst_add, Prod.smul_fst]
  rw [hfun]
  refine ⟨hint, ?_⟩
  have e : (D.u ∘ splitCoord D.n D.m) z =
      logDetGram (D.Y (z'.1 + (0:ℂ) • w'.1)) (D.f (z' + (0:ℂ) • w')) := by
    simp [PeriodChartData.u, z']
  rw [e]; exact hle

end

end GroundTheory.Heights₂.Heights
