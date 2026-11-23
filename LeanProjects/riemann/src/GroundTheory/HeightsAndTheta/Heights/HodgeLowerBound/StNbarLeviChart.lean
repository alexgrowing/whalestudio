import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.ChartVel
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi)

def NbarLeviChart.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B p q : ℕ) (t : ℝ),
    X.M.atlas.Smooth (X.S.regWeight t) →
    ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ w, IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal D.y) z w →
    ∀ k : Fin X.S.R.N, X.M.proj z ∈ X.S.R.mid k →
      ∃ v : Fin D.n → ℂ, IsChartVel X.M (X.S.R.chart k) z w v ∧
        levi (fun y => Real.log ((X.NbarQ B p q t).h y)) z w =
          q * levi (X.S.R.chartFun (X.S.regWeight t) k) (X.S.R.chart k (X.M.proj z)) v +
            p * levi (fun y => Real.log (D.A'.h y)) z w

section Inhabitants

namespace Line

open GroundTheory.Heights₂.Heights (CP)
open GroundTheory.Heights₂.Heights.Regular.ProjectiveLine

theorem isConeTangent_velL :
    IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal yLine) (discL 0) velL := by
  intro f hf
  rw [mCoordIdeal_yLine, Ideal.mem_bot] at hf
  subst hf
  simp

theorem projL_discL_mem_mid : projL (discL 0) ∈ cpMid 0 := by
  have hne : vecL (discL 0) ≠ 0 := vecL_ne_zero (discL_mem 0)
  have h0 : sChart 0 (projL (discL 0)) = 0 := by
    rw [sChart_projL_discL]
    funext j
    simp
  refine ⟨(mem_sChart_source_iff 0 _).2 ⟨?_, ?_⟩, ?_⟩
  · unfold projL
    rw [dif_pos hne, CP.mk_mem_chartDomain]
    simp [vecL, discL]
  · unfold projL
    rw [dif_pos hne, CP.chartCoord_mk]
    have : (fun j : Fin 1 => vecL (discL 0) ((0 : Fin 2).succAbove j) / vecL (discL 0) 0) = 0 := by
      funext j
      simp [vecL, discL]
    rw [this, norm_zero]
    norm_num
  · show sChart 0 (projL (discL 0)) ∈ Metric.ball 0 (7 / 8)
    rw [h0]
    exact Metric.mem_ball_self (by norm_num)

end Line

theorem Line.NbarLeviChart.hyps_inhabited :
    ∃ t : ℝ, 0 < t ∧ (Line.projLineComponentSetting Line.zeroSystem Line.zero_hII).M.atlas.Smooth
      ((Line.projLineComponentSetting Line.zeroSystem Line.zero_hII).S.regWeight t) ∧
    Line.discL 0 ∈ mcPts (mCoordIdeal (Line.lineData Line.zeroSystem Line.zero_hII).y) ∧
    IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal (Line.lineData Line.zeroSystem Line.zero_hII).y)
      (Line.discL 0) Line.velL ∧
    ∃ k : Fin (Line.projLineComponentSetting Line.zeroSystem Line.zero_hII).S.R.N,
      (Line.projLineComponentSetting Line.zeroSystem Line.zero_hII).M.proj (Line.discL 0) ∈
        (Line.projLineComponentSetting Line.zeroSystem Line.zero_hII).S.R.mid k := by
  obtain ⟨t, -, ht, hs, -⟩ := NbarChartSemipos.hyps_of_setting (Line.projLineComponentSetting Line.zeroSystem Line.zero_hII) one_pos
  exact ⟨t, ht, hs, Line.discL_mem 0, Line.isConeTangent_velL, (0 : Fin 2), Line.projL_discL_mem_mid⟩

end Inhabitants

end GroundTheory.Heights₂.Heights.LowerBoundFree
