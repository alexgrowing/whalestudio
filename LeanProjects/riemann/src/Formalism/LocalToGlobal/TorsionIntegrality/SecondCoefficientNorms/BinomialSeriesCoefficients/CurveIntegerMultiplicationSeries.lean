import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveEndoAll
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.PhNormFromDatum
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.ConstantCoeffVecConsPairEqZero
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.Points
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowTwoTorsionWp
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FglInvariant
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CubeThreeR
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.TwoTorsionU
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.ChordEquation

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.C

open Formalism.L2.Th1.A (logSer expSer wpReg xS xPlus)

namespace WeierstrassCurveSeries

variable {K : Type} [Field K] [CharZero K]

theorem logPair (W : WeierstrassCurve K) : IsLogPair (logSer W) (expSer W) := by
  obtain ⟨h0, h1, -, -⟩ := Formalism.L2.Th1.A.logSpec.{0} K W
  obtain ⟨e0, -, e2, e3, -⟩ := Formalism.L2.Th1.A.expSpec.{0} K W
  exact ⟨h0, h1, e0, e3, e2⟩

theorem xIsWp (W : WeierstrassCurve K) : XIsWp (wpReg W) (logSer W) (xS W) (W.b₂ / 12) := by
  have h := Formalism.L2.Th1.A.wpInU.{0} K W
  have hl : PowerSeries.HasSubst (logSer W) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (logPair W).1
  unfold XIsWp wpShift
  rw [map_zero, sub_zero, PowerSeries.subst_add hl, PowerSeries.subst_mul hl,
    PowerSeries.subst_pow hl, PowerSeries.subst_X hl, ← PowerSeries.coe_substAlgHom hl, map_one,
    PowerSeries.coe_substAlgHom hl, h]
  ring

theorem subst_wTr (W : WeierstrassCurve K) (xP yP : K) :
    PowerSeries.subst (logSer W) (wTr W xP yP) = xPlus W xP yP + PowerSeries.C (W.b₂ / 12) := by
  have h := logPair W
  have hl : PowerSeries.HasSubst (logSer W) := PowerSeries.HasSubst.of_constantCoeff_zero' h.1
  unfold wTr
  rw [PowerSeries.subst_add hl, Pts.subst_subst h.2.2.1 h.1, h.2.2.2.1, PowerSeries.X_subst,
    PowerSeries.subst_C]
  rfl

end WeierstrassCurveSeries

open WeierstrassCurveSeries

theorem curve_formal_frame : CurveFrame := by
  intro K _ _ R W hW
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  obtain ⟨-, hx, -, -, hom, -, hF, -⟩ := Formalism.L2.Th1.A.coeffMem.{0} K W R h1 h2 h3 h4 h6
  refine ⟨logPair W, xIsWp W, ⟨(Formalism.L2.Th1.A.wSerFactor.{0} K W).2.2.2.1, hx⟩, ?_, ?_⟩
  · intro n
    have := (Formalism.L2.Th1.A.fglLog.{0} K W).2
    unfold fadd
    rw [← this]
    exact hF n
  · rw [(Formalism.L2.Th1.A.logSpec.{0} K W).2.2.1]
    exact ⟨(Formalism.L2.Th1.A.unitSpec.{0} K W).2.2.1, hom⟩

theorem curveEndoZ_of (hD : CurveSecondLogDerivative) : CurveEndoZ := by
  intro K _ _ W ι _ neg xP yP al h
  obtain ⟨hE, hn, hxy, hsum⟩ := h
  refine ⟨hn, ?_, hsum⟩
  intro P
  have := hD K W (xP P) (yP P) (hE P)
  show HasSecondLogDeriv (wpShift (wpReg W) (xP P + W.b₂ / 12))
    (2 * wpReg W - wTr W (xP P) (yP P) - wTr W (xP (neg P)) (yP (neg P)))
  rw [(hxy P).1, (hxy P).2]
  exact this

theorem curveEndoR_of (hD : CurveSecondLogDerivative) : CurveEndoR := by
  intro K _ _ R W hW ι _ neg xP yP al albar h hx hy hN ha ha' hc
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  have hM := Formalism.L2.Th1.A.coeffMem.{0} K W R h1 h2 h3 h4 h6
  refine ⟨curveEndoZ_of hD K W ι neg xP yP al h, hN, fun P => subst_wTr W _ _, ?_, hx, ha, ha', hc⟩
  intro P n
  exact (hM.2.2.2.2.2.2.2.2.2.2 (xP P) (hx P) (yP P) (hy P) n).1

theorem curveEndoAll_of (hD : CurveSecondLogDerivative) : CurveEndoAll := by
  intro K _ _ _ _ R hR h2 W hW s2 hF1 O _ _ _ τ hτ hstar hself h2O hsum Dn hDn hdata
  obtain ⟨hlp, hwp, hA, hFG, hl'⟩ := curve_formal_frame K R W hW
  have hPh : IsPh (wpReg W) s2 (logSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) :=
    (odd_phi_is_phi K (wpReg W) (logSer W) s2 hlp.1 hlp.2.1).2
  have hFr : Frame R (logSer W) (expSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) :=
    ⟨hlp, hFG, hPh.1⟩
  have hall := endoAllFromData K R hR (wpReg W) s2 (logSer W) (expSer W)
    (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) (xS W) (W.b₂ / 12) hFr hF1 hPh hwp hA O τ hτ hstar
    hself h2 h2O hsum Dn hDn (by
      intro α hα
      obtain ⟨ι, hι, neg, xP, yP, hE, hx, hy, hN, ha, ha', hc, hs⟩ := hdata α hα
      exact ⟨ι, hι, neg, xP, fun P => wTr W (xP P) (yP P), fun P => xPlus W (xP P) (yP P),
        curveEndoR_of hD K R W hW ι neg xP yP (τ α) (τ (star α)) hE hx hy hN ha ha' hc, hs⟩)
  refine ⟨fun α => ⟨(hall α).1, (hall α).2.1, (hall α).2.2, ?_⟩, ?_⟩
  · exact jetAdj K R (logSer W) (expSer W) _ (τ α) (τ (star α)) hlp hPh.1 (hall α).2.2
  · have hm := (hall (-1)).2.1
    rw [star_neg, star_one, map_neg, map_one] at hm
    exact jetOne K R (logSer W) (expSer W) _ hlp hl' hPh.1 hm h2

theorem curve_second_log_derivative_holds : CurveSecondLogDerivative := by
  intro K _ _ W xP yP hP
  exact Formalism.L2.Th1.A.plusZCleared.{0} K W xP yP hP

theorem curve_integer_multiplication_series : CurveEndoZ := curveEndoZ_of curve_second_log_derivative_holds

theorem curve_real_multiplication_series : CurveEndoR := curveEndoR_of curve_second_log_derivative_holds

theorem curve_all_endomorphism_series : CurveEndoAll := curveEndoAll_of curve_second_log_derivative_holds

end Formalism.L2.Th1.C
