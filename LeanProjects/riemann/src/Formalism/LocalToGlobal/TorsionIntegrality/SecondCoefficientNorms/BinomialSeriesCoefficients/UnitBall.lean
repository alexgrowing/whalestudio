import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveEndoUnitBall
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveSecondLogDerivative
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalB
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.TwoTorsionU

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.C

open Formalism.L2.Th1.A (logSer expSer wpReg xS xPlus)

theorem mem_unitBall_iff {K : Type} [NormedField K] [IsUltrametricDist K] (x : K) :
    x ∈ Formalism.G.unitBall K ↔ ‖x‖ ≤ 1 := Iff.rfl

theorem inv_mem_unitBall {K : Type} [NormedField K] [IsUltrametricDist K] {x : K} (h : ‖x‖ = 1) :
    x⁻¹ ∈ Formalism.G.unitBall K := by
  rw [mem_unitBall_iff, norm_inv, h, inv_one]

theorem curve_frame_unit_ball (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K]
    (h2 : ‖(2 : K)‖ = 1) (W : WeierstrassCurve K) (hW : Formalism.L2.Th1.A.IntModel W) (s2 : K) :
    CoeffIn (Formalism.G.unitBall K) W ∧
    Frame (Formalism.G.unitBall K) (logSer W) (expSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) ∧
    F1 (Formalism.G.unitBall K) (logSer W) (expSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) := by
  have hc : CoeffIn (Formalism.G.unitBall K) W := hW
  obtain ⟨hlp, -, -, hfg, -⟩ := curveFrame K (Formalism.G.unitBall K) W hc
  have hph0 : PowerSeries.constantCoeff (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) = 0 :=
    (phOIsPh K (wpReg W) (logSer W) s2 hlp.1 hlp.2.1).2.1
  obtain ⟨hlaw, hinv, -⟩ := Formalism.L2.Th1.A.bridgeLaw K W hW
  have hu := (Formalism.L2.Th1.B.f1O K (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W) s2 (W.b₂ / 12) (wpReg W)
    (logSer W) (Formalism.L2.Th1.A.iSer W) (xS W) (Formalism.L2.Th1.A.fgl W) (Formalism.L2.Th1.A.bridgeWp K W) hlaw
    hinv (Formalism.L2.Th1.A.bridgeCurve K W hW) h2).2.2.1
  exact ⟨hc, ⟨hlp, hfg, hph0⟩,
    (first_level_from_universal_law K (Formalism.L2.Th1.A.fgl W) (logSer W) (expSer W) _ hlp hlaw hph0 hu).2.2⟩

theorem curve_endomorphisms_unit_ball : CurveEndoUnitBall := by
  intro K _ _ _ h2 W hW s2 O _ _ _ τ hτ hstar hsa h2O hsum Dn hDn hdata
  obtain ⟨hc, hfr, hF1⟩ := curve_frame_unit_ball K h2 W hW s2
  have h2R : (2 : K)⁻¹ ∈ Formalism.G.unitBall K := inv_mem_unitBall h2
  have hall := (curveEndoAll K (Formalism.G.unitBall K) (unitBallClosed K) h2R W hc s2 hF1 O τ hτ hstar
    hsa h2O hsum Dn hDn (by
      intro α hα
      obtain ⟨ι, iF, neg, xP, yP, h1, hx, hy, hN, hn, hb, hs⟩ := hdata α hα
      exact ⟨ι, iF, neg, xP, yP, h1, hx, hy, hN, hn.le, inv_mem_unitBall hn, hb, hs⟩)).1
  have hm1 : PhNormAt (Formalism.G.unitBall K) (logSer W) (expSer W)
      (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) (-1) (-1) := by
    have h := (hall (-1)).2.1
    simpa only [star_neg, star_one, map_neg, map_one] using h
  refine ⟨hall, (jetsShape K (Formalism.G.unitBall K) _ _ _ hfr hF1 hm1 h2R).1, ?_⟩
  intro α hα
  have hne : τ α ≠ τ (star α) := by
    intro h
    rw [h, sub_self, norm_zero] at hα
    exact zero_ne_one hα
  exact (jetsUnramified K (Formalism.G.unitBall K) _ _ _ (τ α) (τ (star α)) hfr hF1 hm1 h2R
    (hall α).2.2.1 (inv_mem_unitBall hα) hne).2

end Formalism.L2.Th1.C
