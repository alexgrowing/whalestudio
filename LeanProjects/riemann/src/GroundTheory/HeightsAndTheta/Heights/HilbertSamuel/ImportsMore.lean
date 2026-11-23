import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsBisAlt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics MeasureTheory

theorem TensorPowerL2Degree.proof (hDat : PowerBlockDatum.Statement) (hTop : PowerBlockTop.Statement)
    (hChi : BlockChiCovolume.Statement) (hHS : TheoremHSMBlock.Statement) : TensorPowerL2Degree.Statement := by
  intro K _ ι _ Ω _ _ y D A P0 II hD1 hII har hb hA hc
  classical
  obtain ⟨m, N, v, d, μ, hm, hdy, hk, hv, hgen, hmet, hlat, hμ, hnull, hZ, hnorm⟩ :=
    hDat K ι Ω y D A P0 hD1 har hb hA hc
  have htop : II (Option K) (addIdx ι N) (mCoordIdeal d.y) (D + 1) (fun _ => d.A) =
      (m : ℝ) ^ (D + 1) * II K ι (mCoordIdeal y) (D + 1) (fun _ => A) := by
    rw [hdy]
    refine hTop K ι Ω y D A m N v d.A II hII har hA.semipos.1 hm hv hgen (by rw [d.deg, hk]) d.semipos.1 ?_
    rw [← hdy]
    exact hmet
  obtain ⟨hdef, -⟩ := hHS D (Option K) (addIdx ι N) Ω II d hII
  refine ⟨μ, m, hμ, hnull, hZ, hm, fun ε hε => ?_⟩
  have hfac : (0 : ℝ) < ((D + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hmpos : (0 : ℝ) < (m : ℝ) ^ (D + 1) := pow_pos (by exact_mod_cast hm) _
  have hc' : 0 < ε * (m : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := by positivity
  filter_upwards [hdef.bound hc', hlat] with q hq hl
  intro r ψ hψ hiso _ _
  have hcov := hChi D (Option K) (addIdx ι N) Ω d q (chartLat y A.a (m * q)) (by rw [hk]; exact hl) r ψ hψ
    (fun s f hf hs => by
      rw [hk] at hf
      rw [hiso, ← hs]
      exact hnorm q f hf)
  rw [hcov]
  rw [htop] at hq
  simp only [hsDefect, pw, Real.norm_eq_abs] at hq
  have hq' := (abs_le.mp hq).2
  rw [abs_of_nonneg (by positivity)] at hq'
  push_cast
  rw [mul_pow]
  have key : (II K ι (mCoordIdeal y) (D + 1) (fun _ => A) + ε) *
      ((m : ℝ) ^ (D + 1) * (q : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =
      (m : ℝ) ^ (D + 1) * II K ι (mCoordIdeal y) (D + 1) (fun _ => A) * (q : ℝ) ^ (D + 1) /
          ((D + 1).factorial : ℝ) +
        ε * (m : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) * (q : ℝ) ^ (D + 1) := by
    ring
  rw [key]
  linarith

end GroundTheory.Heights₂.Heights.HilbertSamuel
