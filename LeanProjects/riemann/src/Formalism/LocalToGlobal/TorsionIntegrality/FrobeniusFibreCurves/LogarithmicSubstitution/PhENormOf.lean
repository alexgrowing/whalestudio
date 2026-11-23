import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalD
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveJetsUnitBall
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementI

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.B.Nrm

open Formalism.G (unitBall)
open Formalism.L2.Th1.C (wpShift IsLogPair mulBy PhNormAt Cong LG IntMv IntPS mvExp IsOneUnit XIsWp)
open Formalism.L2.Th1.C.USideB

theorem PhENorm_of (hI : Th0Isogeny) : PhENorm := by
  intro K _ _ _ g2 g3 s2 c0 xT al albar S P l linv i ep F ι _ xQ wp wm hP hT hL hC hxT hxQ hZ hN hS
  have hl := hL.1
  have hsl := hs_of hl
  have hcv : PowerSeries.constantCoeff (mulBy l linv al) = 0 := cc_mulBy hL al
  have hsv := hs_of hcv
  have hS' : (al ^ 2 - 2 * (Fintype.card ι : K)) * s2 = S := by rw [← hN, ← hS]; ring
  have hF := hI K g2 g3 s2 c0 xT al S P ι (fun Q => xQ Q + c0) wp wm hP hT hZ hS'
  obtain ⟨hph0, hphd⟩ :=
    phEDef K s2 (xT + c0) (3 * (xT + c0) ^ 2 - g2 / 4) (wOf (xT + c0) P) l hl
  generalize hn : Fintype.card ι = n at *
  have hthl : PowerSeries.subst l (thTw g2 s2 c0 xT P) = mvExp (-(phTw g2 s2 c0 xT P l)) := hphd
  have hph0' : PowerSeries.constantCoeff (phTw g2 s2 c0 xT P l) = 0 := hph0
  generalize phTw g2 s2 c0 xT P l = ph at *
  generalize thTw g2 s2 c0 xT P = th at *
  set v := mulBy l linv al with hv
  have hnph : PowerSeries.constantCoeff (-ph) = 0 := by simp [hph0']
  have hphv : PowerSeries.constantCoeff (PowerSeries.subst v ph) = 0 := cc_subst hcv hph0'
  have hnphv : PowerSeries.constantCoeff (-(PowerSeries.subst v ph)) = 0 := by simp [hphv]
  have hX : XIsWp P l ep c0 := by
    unfold XIsWp
    rw [Formalism.L2.Th1.C.USideA.subst_wpShift_zero hsl, hC.2.2.1]
    ring

  have h1 : PowerSeries.subst l (PowerSeries.rescale al th) =
      mvExp (-(PowerSeries.subst v ph)) := by
    rw [subst_rescale hL, hthl, Formalism.L2.Th1.C.subst_mvExp hnph hcv]
    have h3 : PowerSeries.subst v (-ph) = -(PowerSeries.subst v ph) := by
      rw [← PowerSeries.coe_substAlgHom hsv, map_neg]
    rw [h3]

  have h4 := congrArg (PowerSeries.subst l) hF
  rw [PowerSeries.subst_mul hsl, PowerSeries.subst_pow hsl, PowerSeries.subst_mul hsl,
    PowerSeries.subst_pow hsl, h1, hthl] at h4
  have h6 : PowerSeries.subst l (∏ Q, wpShift P (xQ Q + c0)) =
      ∏ Q, PowerSeries.subst l (wpShift P (xQ Q + c0)) := by
    rw [← PowerSeries.coe_substAlgHom hsl, map_prod]
  rw [h6] at h4
  have h7 : PowerSeries.X ^ (2 * n) * ∏ Q, PowerSeries.subst l (wpShift P (xQ Q + c0)) =
      (∏ Q, (ep - PowerSeries.C (xQ Q) * PowerSeries.X ^ 2)) * l ^ (2 * n) := by
    rw [pow_mul, pow_mul, ← hn, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_const,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun Q _ => subst_wpShift hl hX (xQ Q)
  have h8 := subst_wpShift hl hX xT
  set B : PowerSeries K := ∏ Q, (ep - PowerSeries.C (xQ Q) * PowerSeries.X ^ 2) with hB
  set G : PowerSeries K := ep - PowerSeries.C xT * PowerSeries.X ^ 2 with hG
  have hl0 : l ^ (2 * n) ≠ 0 := pow_ne_zero _ (l_ne_zero hL)
  have h9 : (mvExp (-(PowerSeries.subst v ph)) : PowerSeries K) * G ^ n =
      mvExp (-ph) ^ (2 * n) * B := by
    apply mul_right_cancel₀ hl0
    calc (mvExp (-(PowerSeries.subst v ph)) : PowerSeries K) * G ^ n * l ^ (2 * n)
        = mvExp (-(PowerSeries.subst v ph)) * (G * l ^ 2) ^ n := by
          rw [mul_pow, ← pow_mul, mul_assoc]
      _ = (mvExp (-(PowerSeries.subst v ph)) *
            PowerSeries.subst l (wpShift P (xT + c0)) ^ n) * PowerSeries.X ^ (2 * n) := by
          rw [← h8]; ring
      _ = mvExp (-ph) ^ (2 * n) *
            (PowerSeries.X ^ (2 * n) * ∏ Q, PowerSeries.subst l (wpShift P (xQ Q + c0))) := by
          rw [h4]; ring
      _ = _ := by rw [h7]; ring

  have hepi : ep ∈ intSub (unitBall K) := fun k => hC.1 (Finsupp.single () k)
  have hBi : B ∈ intSub (unitBall K) :=
    Subring.prod_mem _ fun Q _ => Subring.sub_mem _ hepi
      (Subring.mul_mem _ (C_mem_intSub (hxQ Q)) (Subring.pow_mem _ (X_mem_intSub _) 2))
  have hGi : G ∈ intSub (unitBall K) :=
    Subring.sub_mem _ hepi
      (Subring.mul_mem _ (C_mem_intSub hxT) (Subring.pow_mem _ (X_mem_intSub _) 2))
  have hB1 : PowerSeries.constantCoeff B = 1 := by
    rw [hB, map_prod]
    apply Finset.prod_eq_one
    intro Q _
    simp [hC.2.1]
  have hNph : (al * albar) • ph = ((2 * n : ℕ) : K) • ph := by rw [hN]; push_cast; rfl
  have hNph0 : PowerSeries.constantCoeff (((2 * n : ℕ) : K) • ph) = 0 := by simp [hph0']
  have h10 : (mvExp (PowerSeries.subst v ph - (al * albar) • ph) : PowerSeries K) * B = G ^ n := by
    rw [hNph, Formalism.L2.Th1.C.mvExp_sub hphv hNph0, ← smul_neg,
      Formalism.L2.Th1.C.mvExp_smul_nat hnph, mul_assoc, ← h9, ← mul_assoc,
      Formalism.L2.Th1.C.mvExp_mul_neg hphv, one_mul]
  have h11 : IntPS (unitBall K) (mvExp (PowerSeries.subst v ph - (al * albar) • ph)) :=
    int_of_mul ⟨hB1, hBi⟩ (Subring.pow_mem _ hGi n) h10
  refine ⟨?_, intMv_of_intPS h11⟩
  have : PowerSeries.constantCoeff (PowerSeries.subst v ph - (al * albar) • ph) = 0 := by
    simp [hphv, hph0']
  exact this

end Formalism.L2.Th1.B.Nrm
