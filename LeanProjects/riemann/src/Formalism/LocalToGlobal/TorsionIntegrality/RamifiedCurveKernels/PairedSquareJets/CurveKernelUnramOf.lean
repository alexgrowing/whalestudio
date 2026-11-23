import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementU
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.FinalA
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveSecondLogDerivative

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.G

open Formalism.L2.Th1.C
open Formalism.L2.Th1.A (logSer expSer wpReg xS)
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (jetPair)
open WeierstrassCurveSeries

theorem curveJetsUnram (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K]
    (W : WeierstrassCurve K) (hc : CoeffIn (unitBall K) W) (h2 : ‖(2 : K)‖ = 1)
    (s2 al albar : K) (t : ℤ) (ι : Type) [Fintype ι] (neg : ι → ι) (xP yP : ι → K)
    (hE : IsEndoCurve W neg xP yP al) (hx : ∀ P, ‖xP P‖ ≤ 1) (hy : ∀ P, ‖yP P‖ ≤ 1)
    (hNal : al * albar = (Fintype.card ι : K) + 1) (hal : ‖al‖ = 1) (ht : al + albar = (t : K))
    (hd : ‖al - albar‖ = 1) (hb : ‖(al ^ 2 - 1) * (W.b₂ / 12)‖ ≤ 1)
    (hs : al * (al - albar) * s2 = ∑ P, (xP P + W.b₂ / 12)) :
    ∀ i : ℕ, 1 ≤ i → ‖jet (logSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) i‖ ≤ 1 := by
  obtain ⟨hlp, hwp, hAx, hFG, -⟩ := curveFrame K (unitBall K) W hc
  have hPh : IsPh (wpReg W) s2 (logSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) :=
    (phOIsPh K (wpReg W) (logSer W) s2 hlp.1 hlp.2.1).2
  have hFr : Frame (unitBall K) (logSer W) (expSer W)
      (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) := ⟨hlp, hFG, hPh.1⟩
  have h2R : (2 : K)⁻¹ ∈ unitBall K := inv_mem_unitBall h2
  have hal0 : al ≠ 0 := by
    intro h
    rw [h, norm_zero] at hal
    exact zero_ne_one hal
  have halR : al ∈ unitBall K := hal.le
  have halI : al⁻¹ ∈ unitBall K := inv_mem_unitBall hal
  have hDat := curveEndoR K (unitBall K) W hc ι neg xP yP al albar hE hx hy hNal halR halI hb
  have hEal : EndInt (unitBall K) (logSer W) (expSer W) al :=
    endIntFromDatum K (unitBall K) (wpReg W) (logSer W) (expSer W) (xS W) (W.b₂ / 12) ι neg xP _ _
      al albar hlp hwp hAx h2R hDat
  have hEbar : EndInt (unitBall K) (logSer W) (expSer W) albar := by
    obtain ⟨-, -, -, -, hm, hadd, hmul⟩ := ptClosure K (unitBall K) (logSer W) (expSer W) hlp hFG
    have h := hadd _ _ (endInt_int (unitBall K) _ _ hlp hFG t) (hmul _ _ hm hEal)
    have he : (t : K) + -1 * al = albar := by rw [← ht]; ring
    rwa [he] at h
  have hNorm : PhNormAt (unitBall K) (logSer W) (expSer W)
      (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) al albar :=
    phNormFromDatum K (unitBall K) (wpReg W) s2 (logSer W) (expSer W) _ (xS W) (W.b₂ / 12) ι neg xP
      _ _ al albar hlp hPh hwp hAx h2R hDat hs
  have hF1 := weierstrass_biadditive_mod_equiv K W hc h2 s2
  have hAdj : AdjAt (unitBall K) (logSer W) (expSer W)
      (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) al albar :=
    adjUnitNorm K (unitBall K) (logSer W) (expSer W) _ al albar ((Fintype.card ι : ℤ) + 1) hFr hF1
      hal0 halI hEal hEbar (by rw [hNal]; push_cast; ring) hNorm
  have hne : al ≠ albar := by
    intro h
    rw [h, sub_self, norm_zero] at hd
    exact zero_ne_one hd
  exact (jetsUnramified K (unitBall K) (logSer W) (expSer W) _ al albar hFr hF1
    (curveNegNorm K (unitBall K) W hc h2R s2) h2R hAdj (inv_mem_unitBall hd) hne).1

theorem CurveKernelUnram_of (hK : KernelTwo) : CurveKernelUnram := by
  intro K _ _ _ W hc h2 s2 al albar t ι _ neg xP yP hE hx hy hNal hal ht hd hb hs n _ c hcn G hG P hP
  obtain ⟨hlp, -, -, -, hU⟩ := curveFrame K (unitBall K) W hc
  have hph0 : PowerSeries.constantCoeff (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) = 0 :=
    (phOIsPh K (wpReg W) (logSer W) s2 hlp.1 hlp.2.1).2.1
  exact (hK K (logSer W) (expSer W) _ hlp hU hph0
    (curveJetsUnram K W hc h2 s2 al albar t ι neg xP yP hE hx hy hNal hal ht hd hb hs)
    n c hcn G hG).2 P hP

end Formalism.L2.Th1.G
