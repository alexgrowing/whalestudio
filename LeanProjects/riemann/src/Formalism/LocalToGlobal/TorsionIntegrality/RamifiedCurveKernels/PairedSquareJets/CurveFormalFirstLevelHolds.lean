import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementR
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveSecondLogDerivative
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalB
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.TwoTorsionU

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.G

open Formalism.L2.Th1.C
open Formalism.L2.Th1.A (logSer expSer wpReg xS xPlus)
open Formalism.G (unitBall)

namespace WeierstrassCurveSeries

theorem rescale_neg_one_of_even {K : Type} [Field K] (e : PowerSeries K)
    (h : ∀ n : ℕ, Odd n → PowerSeries.coeff n e = 0) : PowerSeries.rescale (-1 : K) e = e := by
  ext n
  rw [PowerSeries.coeff_rescale]
  rcases Nat.even_or_odd n with hn | hn
  · rw [hn.neg_one_pow, one_mul]
  · rw [h n hn, mul_zero]

theorem endoCurve_neg_one {K : Type} [Field K] [CharZero K] (W : WeierstrassCurve K) :
    IsEndoCurve W (id : Empty → Empty) (fun _ => (0 : K)) (fun _ => (0 : K)) (-1) := by
  refine ⟨fun P => P.elim, fun P => P.elim, fun P => P.elim, ?_⟩
  rw [rescale_neg_one_of_even _ (Formalism.L2.Th1.A.wpShape.{0} K W).2.2.1]
  simp

theorem inv_mem_unitBall {K : Type} [NormedField K] [IsUltrametricDist K] {x : K} (h : ‖x‖ = 1) :
    x⁻¹ ∈ unitBall K := by
  have h1 : ‖x⁻¹‖ ≤ 1 := by rw [norm_inv, h, inv_one]
  first
    | exact h1
    | simpa [Formalism.G.unitBall] using h1

theorem endInt_int {K : Type} [Field K] (R : Subring K) (l linv : PowerSeries K)
    (hl : IsLogPair l linv) (hF : FGInt R l linv) (n : ℤ) : EndInt R l linv (n : K) := by
  obtain ⟨-, -, h0, h1, hm, hadd, -⟩ := ptClosure K R l linv hl hF
  induction n using Int.induction_on with
  | zero => simpa using h0
  | succ i ih =>
    have := hadd _ _ ih h1
    simpa using this
  | pred i ih =>
    have := hadd _ _ ih hm
    simpa [sub_eq_add_neg] using this

end WeierstrassCurveSeries

open WeierstrassCurveSeries

theorem curve_neg_norm_holds : CurveNegNorm := by
  intro K _ _ R W hW h2 s2
  obtain ⟨hlp, hwp, hA, -, -⟩ := curveFrame K R W hW
  have hPh : IsPh (wpReg W) s2 (logSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) :=
    (phOIsPh K (wpReg W) (logSer W) s2 hlp.1 hlp.2.1).2
  have hm : (-1 : K) ∈ R := R.neg_mem R.one_mem
  have hE := curveEndoR K R W hW Empty id (fun _ => (0 : K)) (fun _ => (0 : K)) (-1) (-1)
    (endoCurve_neg_one W) (fun P => P.elim) (fun P => P.elim) (by simp) hm
    (by rw [inv_neg, inv_one]; exact hm) (by simp)
  exact phNormFromDatum K R (wpReg W) s2 (logSer W) (expSer W) _ (xS W) (W.b₂ / 12) Empty id _ _ _
    (-1) (-1) hlp hPh hwp hA h2 hE (by simp)

theorem curve_formal_first_level_holds : WeierstrassBiadditiveModEquiv := by
  intro K _ _ _ W hc h2 s2
  have hW : Formalism.L2.Th1.A.IntModel W := hc
  obtain ⟨hlp, -, -, -, -⟩ := curveFrame K (unitBall K) W hc
  have hph0 : PowerSeries.constantCoeff (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) = 0 :=
    (phOIsPh K (wpReg W) (logSer W) s2 hlp.1 hlp.2.1).2.1
  obtain ⟨hlaw, hinv, -⟩ := Formalism.L2.Th1.A.bridgeLaw K W hW
  have hu := (Formalism.L2.Th1.B.f1O K (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W) s2 (W.b₂ / 12) (wpReg W)
    (logSer W) (Formalism.L2.Th1.A.iSer W) (xS W) (Formalism.L2.Th1.A.fgl W) (Formalism.L2.Th1.A.bridgeWp K W) hlaw
    hinv (Formalism.L2.Th1.A.bridgeCurve K W hW) h2).2.2.1
  exact (first_level_from_universal_law K (Formalism.L2.Th1.A.fgl W) (logSer W) (expSer W) _ hlp hlaw hph0 hu).2.2

theorem CurveRamified_of (hR : RamifiedShape) (hA : AdjUnitNorm) (_hI : InvEndInt)
    (hN : CurveNegNorm) (hF : WeierstrassBiadditiveModEquiv) : CurveRamified := by
  intro K _ _ _ W hc h2 s2 al albar d t ι _ neg xP yP hE hx hy hNal hal ht hd hd0 hb hs
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
  have hF1 := hF K W hc h2 s2
  have hAdj : AdjAt (unitBall K) (logSer W) (expSer W)
      (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) al albar :=
    hA K (unitBall K) (logSer W) (expSer W) _ al albar ((Fintype.card ι : ℤ) + 1) hFr hF1 hal0 halI
      hEal hEbar (by rw [hNal]; push_cast; ring) hNorm
  exact hR K (logSer W) (expSer W) _ al albar d hFr hF1 (hN K (unitBall K) W hc h2R s2) h2 hAdj hd
    hd0

theorem CurveRamified_of_shape (hR : RamifiedShape) (hA : AdjUnitNorm) (hI : InvEndInt) :
    CurveRamified := CurveRamified_of hR hA hI curve_neg_norm_holds curve_formal_first_level_holds

end Formalism.L2.Th1.G
