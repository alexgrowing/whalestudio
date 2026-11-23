import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementP
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementT
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.FlowBasic
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.FlowTrans
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.Laurent
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.CurveSer

open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

namespace Plus

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (xP yP : R)

theorem tDen_cc : constantCoeff (tDen W xP) = 1 := by
  simp [tDen, xS, PowerSeries.constantCoeff_invOfUnit]

theorem tDen_mul_inv : tDen W xP * invOfUnit (tDen W xP) 1 = 1 := PowerSeries.mul_invOfUnit _ _ (by simpa using tDen_cc W xP)

theorem inv_cc : constantCoeff (invOfUnit (tDen W xP) 1) = 1 := by
  simp [PowerSeries.constantCoeff_invOfUnit]

theorem toL_tDen_mul_inv : toL (tDen W xP) * toL (invOfUnit (tDen W xP) 1) = 1 := by
  rw [← map_mul, tDen_mul_inv, map_one]

theorem toL_X_mul : (toL X : LaurentSeries R) * uPow (-1) = 1 := by
  simp [uPow, HahnSeries.ofPowerSeries_X, HahnSeries.single_mul_single, HahnSeries.single_zero_one]

theorem uPow_neg_two : (uPow (-2) : LaurentSeries R) = uPow (-1) ^ 2 := by
  simp only [uPow]
  rw [sq, HahnSeries.single_mul_single]
  norm_num

theorem uPow_neg_three : (uPow (-3) : LaurentSeries R) = uPow (-1) ^ 3 := by
  simp only [uPow]
  rw [pow_three, HahnSeries.single_mul_single, HahnSeries.single_mul_single]
  norm_num

theorem xL_eq : xL W = uPow (-1) ^ 2 * toL (xS W) := by
  rw [xL, uPow_neg_two]

theorem yL_eq : yL W = uPow (-1) ^ 3 * toL (yS W) := by
  rw [yL, uPow_neg_three]

theorem toL_tDen : toL (tDen W xP) = toL (xS W) - HahnSeries.C xP * toL X ^ 2 := by
  simp only [tDen, map_sub, map_mul, map_pow, HahnSeries.ofPowerSeries_C]

theorem toL_tS : toL (tS W xP) = toL X ^ 2 * toL (invOfUnit (tDen W xP) 1) := by
  simp only [tS, map_mul, map_pow]

theorem xL_sub : xL W - HahnSeries.C xP = uPow (-1) ^ 2 * toL (tDen W xP) := by
  rw [toL_tDen, xL_eq, mul_sub]
  have h : (uPow (-1) : LaurentSeries R) ^ 2 * (HahnSeries.C xP * toL X ^ 2) = HahnSeries.C xP := by
    rw [mul_left_comm, ← mul_pow, mul_comm (uPow (-1) : LaurentSeries R) (toL X), toL_X_mul,
      one_pow, mul_one]
  rw [h]

theorem yL_sub : yL W - HahnSeries.C yP = uPow (-1) ^ 3 * toL (yS W - C yP * X ^ 3) := by
  rw [yL_eq, map_sub, map_mul, map_pow, HahnSeries.ofPowerSeries_C, mul_sub]
  have h : (uPow (-1) : LaurentSeries R) ^ 3 * (HahnSeries.C yP * toL X ^ 3) = HahnSeries.C yP := by
    rw [mul_left_comm, ← mul_pow, mul_comm (uPow (-1) : LaurentSeries R) (toL X), toL_X_mul,
      one_pow, mul_one]
  rw [h]

theorem toL_tS_mul : toL (tS W xP) * (xL W - HahnSeries.C xP) = 1 := by
  rw [xL_sub, toL_tS]
  calc (toL X : LaurentSeries R) ^ 2 * toL (invOfUnit (tDen W xP) 1) * (uPow (-1) ^ 2 * toL (tDen W xP))
      = ((toL X : LaurentSeries R) * uPow (-1)) ^ 2
          * (toL (tDen W xP) * toL (invOfUnit (tDen W xP) 1)) := by ring
    _ = 1 := by rw [toL_X_mul, toL_tDen_mul_inv, one_pow, one_mul]

theorem coeff_two_tS : coeff 2 (tS W xP) = 1 := by
  simp [tS, PowerSeries.coeff_X_pow_mul', inv_cc]

theorem toL_nS : toL (nS W xP yP) =
    HahnSeries.C (W.a₄ - W.a₁ * yP + 2 * W.a₂ * xP + 3 * xP ^ 2) * toL X * toL (xS W)
      - HahnSeries.C (2 * yP + W.a₁ * xP + W.a₃) * toL (yS W)
      + HahnSeries.C (2 * W.a₆ + W.a₄ * xP - W.a₃ * yP - xP ^ 3) * toL X ^ 3 := by
  simp only [nS, map_add, map_sub, map_mul, map_pow, HahnSeries.ofPowerSeries_C]

theorem toL_xPlus : toL (xPlus W xP yP) = HahnSeries.C xP
    + toL X * toL (nS W xP yP) * toL (invOfUnit (tDen W xP) 1) ^ 2 := by
  simp only [xPlus, map_add, map_mul, map_pow, HahnSeries.ofPowerSeries_C]

theorem toL_yPlus : toL (yPlus W xP yP) =
    -(toL (yS W - C yP * X ^ 3) * toL (nS W xP yP) * toL (invOfUnit (tDen W xP) 1) ^ 3)
      - HahnSeries.C yP - HahnSeries.C W.a₁ * toL (xPlus W xP yP) - HahnSeries.C W.a₃ := by
  simp only [yPlus, map_add, map_sub, map_neg, map_mul, map_pow, HahnSeries.ofPowerSeries_C]

def subHom (s : R⟦X⟧) (hs : constantCoeff s = 0) : R⟦X⟧ →ₐ[R] R⟦X⟧ :=
  substAlgHom (HasSubst.of_constantCoeff_zero' hs)

theorem subHom_apply (s : R⟦X⟧) (hs : constantCoeff s = 0) (f : R⟦X⟧) :
    subHom s hs f = f.subst s := by
  simp only [subHom, PowerSeries.coe_substAlgHom]

theorem subHom_X (s : R⟦X⟧) (hs : constantCoeff s = 0) : subHom s hs X = s := by
  rw [subHom_apply, PowerSeries.subst_X (HasSubst.of_constantCoeff_zero' hs)]

theorem subHom_C (s : R⟦X⟧) (hs : constantCoeff s = 0) (a : R) : subHom s hs (C a) = C a := by
  exact (subHom s hs).commutes a

theorem inv_subst (hI : ISerSpec.{u}) :
    (invOfUnit (tDen W xP) 1).subst (iSer W) = iDen W ^ 2 * invOfUnit (tDen W xP) 1 := by
  obtain ⟨hs0, -, -, -, hx, -, -, -⟩ := hI R W
  have hS : HasSubst (iSer W) := HasSubst.of_constantCoeff_zero' hs0
  have hw0 : constantCoeff (wSer W) = 0 := (Formalism.ELL.wSeriesUnique R W).choose_spec.1.1
  have hB : iDen W * invOfUnit (iDen W) (-1) = 1 :=
    PowerSeries.mul_invOfUnit _ _ (by simp [iDen, hw0])
  have hC := tDen_mul_inv W xP
  have hCs : (C xP : R⟦X⟧).subst (iSer W) = C xP := by
    rw [← PowerSeries.coe_substAlgHom hS]
    exact (PowerSeries.substAlgHom hS).commutes xP
  have hT : (tDen W xP).subst (iSer W) = invOfUnit (iDen W) (-1) ^ 2 * tDen W xP := by
    rw [tDen, ← PowerSeries.coe_substAlgHom hS, map_sub, map_mul, map_pow, PowerSeries.coe_substAlgHom,
      PowerSeries.subst_X hS, hCs, hx, iSer]
    ring
  have hA : (tDen W xP).subst (iSer W) * (invOfUnit (tDen W xP) 1).subst (iSer W) = 1 := by
    rw [← PowerSeries.coe_substAlgHom hS, ← map_mul, hC, map_one]
  rw [hT] at hA
  linear_combination (-((invOfUnit (tDen W xP) 1).subst (iSer W) * (iDen W * invOfUnit (iDen W) (-1) + 1) * tDen W xP * invOfUnit (tDen W xP) 1)) * hB
    - (invOfUnit (tDen W xP) 1).subst (iSer W) * hC + iDen W ^ 2 * invOfUnit (tDen W xP) 1 * hA

theorem tS_subst (hI : ISerSpec.{u}) : (tS W xP).subst (iSer W) = tS W xP := by
  obtain ⟨hs0, -, -, -, -, -, -, -⟩ := hI R W
  have hS : HasSubst (iSer W) := HasSubst.of_constantCoeff_zero' hs0
  have hw0 : constantCoeff (wSer W) = 0 := (Formalism.ELL.wSeriesUnique R W).choose_spec.1.1
  have hB : iDen W * invOfUnit (iDen W) (-1) = 1 :=
    PowerSeries.mul_invOfUnit _ _ (by simp [iDen, hw0])
  rw [tS, ← PowerSeries.coe_substAlgHom hS, map_mul, map_pow, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X hS, inv_subst W xP hI, iSer]
  linear_combination (X ^ 2 * invOfUnit (tDen W xP) 1 * (iDen W * invOfUnit (iDen W) (-1) + 1)) * hB

theorem nS_subst (hI : ISerSpec.{u}) : (nS W xP yP).subst (iSer W)
    = invOfUnit (iDen W) (-1) ^ 3 * nS W xP (W.toAffine.negY xP yP) := by
  obtain ⟨hs0, -, -, -, hx, hy, -, -⟩ := hI R W
  have hS : HasSubst (iSer W) := HasSubst.of_constantCoeff_zero' hs0
  have hCs : ∀ r : R, (C r : R⟦X⟧).subst (iSer W) = C r := fun r => by
    rw [← PowerSeries.coe_substAlgHom hS]
    exact (PowerSeries.substAlgHom hS).commutes r
  rw [nS, nS, ← PowerSeries.coe_substAlgHom hS]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg]
  simp only [PowerSeries.coe_substAlgHom, PowerSeries.subst_X hS, hCs, hx, hy]
  simp only [iSer, WeierstrassCurve.Affine.negY, map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat]
  ring

theorem xPlus_subst (hI : ISerSpec.{u}) :
    (xPlus W xP yP).subst (iSer W) = xPlus W xP (W.toAffine.negY xP yP) := by
  obtain ⟨hs0, -, -, -, -, -, -, -⟩ := hI R W
  have hS : HasSubst (iSer W) := HasSubst.of_constantCoeff_zero' hs0
  have hw0 : constantCoeff (wSer W) = 0 := (Formalism.ELL.wSeriesUnique R W).choose_spec.1.1
  have hB : iDen W * invOfUnit (iDen W) (-1) = 1 :=
    PowerSeries.mul_invOfUnit _ _ (by simp [iDen, hw0])
  have hCs : (C xP : R⟦X⟧).subst (iSer W) = C xP := by
    rw [← PowerSeries.coe_substAlgHom hS]
    exact (PowerSeries.substAlgHom hS).commutes xP
  rw [xPlus, xPlus, ← PowerSeries.coe_substAlgHom hS, map_add, map_mul, map_mul, map_pow,
    PowerSeries.coe_substAlgHom, PowerSeries.subst_X hS, hCs, nS_subst W xP yP hI, inv_subst W xP hI, iSer]
  linear_combination (X * nS W xP (W.toAffine.negY xP yP) * invOfUnit (tDen W xP) 1 ^ 2 * (iDen W * invOfUnit (iDen W) (-1) + 1) * ((iDen W * invOfUnit (iDen W) (-1)) ^ 2 + 1)) * hB

theorem equation_C {xP yP : R} (hP : W.toAffine.Equation xP yP) :
    (curveL W).toAffine.Equation (HahnSeries.C xP) (HahnSeries.C yP) := by
  rw [WeierstrassCurve.Affine.equation_iff] at hP ⊢
  have h := congrArg (HahnSeries.C : R →+* LaurentSeries R) hP
  simpa using h

theorem chord (hFL : FlowL.{u}) {xP yP : R} (hP : W.toAffine.Equation xP yP) :
    toL (xPlus W xP yP) = (curveL W).toAffine.addX (xL W) (HahnSeries.C xP) (slopeL W xP yP) ∧
    toL (yPlus W xP yP)
      = (curveL W).toAffine.addY (xL W) (HahnSeries.C xP) (yL W) (slopeL W xP yP) := by
  obtain ⟨hX, hY⟩ := chordFormula _ (curveL W) (xL W) (yL W) (HahnSeries.C xP)
    (HahnSeries.C yP) (toL (tS W xP)) (hFL R W).1.1 (equation_C W hP) (toL_tS_mul W xP)
  have h : (toL X : LaurentSeries R) * uPow (-1) = 1 := toL_X_mul
  have hx : toL (xPlus W xP yP)
      = (curveL W).toAffine.addX (xL W) (HahnSeries.C xP) (slopeL W xP yP) := by
    rw [slopeL, hX, toL_xPlus, toL_nS, toL_tS, xL_eq, yL_eq]
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, map_add, map_sub, map_mul, map_pow,
      map_ofNat]
    generalize toL (invOfUnit (tDen W xP) 1) = v
    generalize toL (xS W) = xs
    generalize toL (yS W) = ys
    linear_combination (-(HahnSeries.C W.a₄ - HahnSeries.C W.a₁ * HahnSeries.C yP
        + 2 * HahnSeries.C W.a₂ * HahnSeries.C xP + 3 * HahnSeries.C xP ^ 2) * xs * v ^ 2
          * toL X ^ 2 * (toL X * uPow (-1) + 1)
      + (2 * HahnSeries.C yP + HahnSeries.C W.a₁ * HahnSeries.C xP + HahnSeries.C W.a₃) * ys
          * v ^ 2 * toL X * ((toL X * uPow (-1)) ^ 2 + toL X * uPow (-1) + 1)) * h
  refine ⟨hx, ?_⟩
  rw [slopeL] at hx ⊢
  rw [hY, ← hx, toL_yPlus, yL_sub, toL_tS]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
  rw [toL_xPlus]
  linear_combination (toL (yS W - C yP * X ^ 3) * toL (nS W xP yP)
    * toL (invOfUnit (tDen W xP) 1) ^ 3 * ((toL X * uPow (-1)) ^ 2 + toL X * uPow (-1) + 1)) * h

theorem isFlow_of_toL (hDL : DLSpec.{u}) {a b : R⟦X⟧}
    (h : IsFlow (curveL W) (DL W) (toL a) (toL b)) : IsFlow (curveS W) (D W) a b := by
  obtain ⟨hE, h1, h2⟩ := h
  obtain ⟨-, -, -, hD⟩ := hDL R W
  have inj : Function.Injective (toL : R⟦X⟧ →+* LaurentSeries R) := HahnSeries.ofPowerSeries_injective
  refine ⟨?_, ?_, ?_⟩
  · rw [WeierstrassCurve.Affine.equation_iff] at hE ⊢
    apply inj
    simpa using hE
  · apply inj
    rw [← hD]
    simpa [map_ofNat toL 2] using h1
  · apply inj
    rw [← hD]
    simpa [map_ofNat toL 2, map_ofNat toL 3] using h2

theorem nS_cc : constantCoeff (nS W xP yP) = 2 * yP + W.a₁ * xP + W.a₃ := by
  simp [nS, yS, xS, PowerSeries.constantCoeff_invOfUnit]

theorem xPlus_cc : constantCoeff (xPlus W xP yP) = xP := by
  simp [xPlus]

theorem yPlus_cc : constantCoeff (yPlus W xP yP) = yP := by
  simp [yPlus, yS, xS, xPlus_cc, nS_cc, PowerSeries.constantCoeff_invOfUnit] <;> ring

section Map

variable {S : Type v} [CommRing S] (φ : R →+* S)

theorem map_tDen : PowerSeries.map φ (tDen W xP) = tDen (W.map φ) (φ xP) := by
  simp only [tDen, map_sub, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X, CurveSer.map_xS]

theorem map_inv : PowerSeries.map φ (invOfUnit (tDen W xP) 1)
    = invOfUnit (tDen (W.map φ) (φ xP)) 1 := by
  have h1 : tDen (W.map φ) (φ xP) * PowerSeries.map φ (invOfUnit (tDen W xP) 1) = 1 := by
    rw [← Plus.map_tDen W xP φ, ← map_mul, tDen_mul_inv, map_one]
  have h2 := tDen_mul_inv (W.map φ) (φ xP)
  calc PowerSeries.map φ (invOfUnit (tDen W xP) 1)
      = (invOfUnit (tDen (W.map φ) (φ xP)) 1 * tDen (W.map φ) (φ xP))
          * PowerSeries.map φ (invOfUnit (tDen W xP) 1) := by
        rw [mul_comm (invOfUnit (tDen (W.map φ) (φ xP)) 1) (tDen (W.map φ) (φ xP)), h2, one_mul]
    _ = invOfUnit (tDen (W.map φ) (φ xP)) 1 := by rw [mul_assoc, h1, mul_one]

theorem map_tS : PowerSeries.map φ (tS W xP) = tS (W.map φ) (φ xP) := by
  simp only [tS, map_mul, map_pow, PowerSeries.map_X, Plus.map_inv W xP φ]

theorem map_nS : PowerSeries.map φ (nS W xP yP) = nS (W.map φ) (φ xP) (φ yP) := by
  simp only [nS, yS, map_add, map_sub, map_mul, map_neg, map_pow, PowerSeries.map_C, PowerSeries.map_X,
    CurveSer.map_xS, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, map_ofNat]

theorem map_xPlus : PowerSeries.map φ (xPlus W xP yP) = xPlus (W.map φ) (φ xP) (φ yP) := by
  simp only [xPlus, map_add, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X,
    Plus.map_nS W xP yP φ, Plus.map_inv W xP φ]

theorem map_yPlus : PowerSeries.map φ (yPlus W xP yP) = yPlus (W.map φ) (φ xP) (φ yP) := by
  simp only [yPlus, yS, map_add, map_sub, map_neg, map_mul, map_pow, PowerSeries.map_C,
    PowerSeries.map_X, CurveSer.map_xS, Plus.map_nS W xP yP φ, Plus.map_inv W xP φ,
    Plus.map_xPlus W xP yP φ, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]

end Map

end Plus

open Plus

theorem tSpec_of (hI : ISerSpec.{u}) : TSpec.{u} := by
  intro R _ W xP
  exact ⟨Plus.tDen_cc W xP, Plus.tDen_mul_inv W xP, Plus.toL_tS_mul W xP, Plus.coeff_two_tS W xP,
    ⟨invOfUnit (tDen W xP) 1, rfl⟩, Plus.tS_subst W xP hI⟩

theorem plusChord_of (hFL : FlowL.{u}) : PlusChord.{u} := by
  intro R _ W xP yP hP
  exact Plus.chord W hFL hP

theorem plusFlow_of (hDL : DLSpec.{u}) (hFL : FlowL.{u}) : PlusFlow.{u} := by
  intro R _ W xP yP hP
  obtain ⟨hDer, hConst, hC, -⟩ := hDL R W
  obtain ⟨hx, hy⟩ := chord W hFL hP
  have h := flowTranslation _ (curveL W) (DL W) (xL W) (yL W) (HahnSeries.C xP)
    (HahnSeries.C yP) (toL (tS W xP)) hDer hConst (hFL R W).1 (equation_C W hP) (hC xP) (hC yP)
    (toL_tS_mul W xP)
  rw [slopeL] at hx hy
  rw [← hx, ← hy] at h
  exact ⟨isFlow_of_toL W hDL h, xPlus_cc W xP yP, yPlus_cc W xP yP⟩

theorem plusLogDeriv_of (hDL : DLSpec.{u}) (hFL : FlowL.{u}) : PlusLogDeriv.{u} := by
  intro R _ W xP yP hP
  obtain ⟨hDer, hConst, hC, -⟩ := hDL R W
  have hx := (chord W hFL hP).1
  have hx' := (chord W hFL ((WeierstrassCurve.Affine.equation_neg xP yP).2 hP)).1
  have h := flowLogDerivative _ (curveL W) (DL W) (xL W) (yL W) (HahnSeries.C xP)
    (HahnSeries.C yP) (toL (tS W xP)) hDer hConst (hFL R W).1 (equation_C W hP) (hC xP) (hC yP)
    (toL_tS_mul W xP)
  rw [WeierstrassCurve.Affine.map_negY] at h
  rw [slopeL] at hx hx'
  rw [hx, hx', h]

theorem plusNeg_of (hI : ISerSpec.{u}) : PlusNeg.{u} := by
  intro R _ W xP yP _
  exact Plus.xPlus_subst W xP yP hI

theorem addition_map : PlusMap.{u, v} := by
  intro R S _ _ φ W xP yP
  exact ⟨Plus.map_tS W xP φ, Plus.map_xPlus W xP yP φ, Plus.map_yPlus W xP yP φ⟩

end Formalism.L2.Th1.A
