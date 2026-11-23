import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementN
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FglInvariant

open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

namespace Nn

section Unique

variable {R : Type u} [CommRing R]

theorem X_pow_succ_dvd_of_derivative
    (hR : ∀ (n : ℕ) (r : R), n ≠ 0 → (n : R) * r = 0 → r = 0) {f : R⟦X⟧} {n : ℕ}
    (h0 : constantCoeff f = 0) (h : X ^ n ∣ derivative R f) : X ^ (n + 1) ∣ f := by
  rw [PowerSeries.X_pow_dvd_iff] at h ⊢
  intro m hm
  rcases m with _ | k
  · simpa using h0
  · have hk := h k (by omega)
    rw [PowerSeries.coeff_derivative] at hk
    apply hR (k + 1) _ (Nat.succ_ne_zero k)
    rw [mul_comm]
    exact_mod_cast hk

theorem eq_zero_of_forall_X_pow_dvd {f : R⟦X⟧} (h : ∀ n : ℕ, X ^ n ∣ f) : f = 0 := by
  ext n
  have h1 := (PowerSeries.X_pow_dvd_iff).mp (h (n + 1)) n (Nat.lt_succ_self n)
  simpa using h1

end Unique

end Nn

open Nn

theorem flow_unique : FlowUnique.{u} := by
  rintro R _ W x y x' y' hR ⟨-, hx, hy⟩ ⟨-, hx', hy'⟩ h0x h0y
  have hfo : fw W * om W = 1 := (invariant_differential_units R W).2.1
  have eD : ∀ g : R⟦X⟧, derivative R g = om W * D W g := fun g => by
    simp only [D, Derivation.smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_comm (om W), hfo, one_mul]
  have key : ∀ n : ℕ, X ^ n ∣ x - x' ∧ X ^ n ∣ y - y' := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := ih
      constructor
      · apply X_pow_succ_dvd_of_derivative hR (by rw [map_sub, h0x, sub_self])
        refine ⟨om W * (2 * b + (curveS W).a₁ * a), ?_⟩
        rw [map_sub, eD x, eD x', hx, hx']
        linear_combination (2 * om W) * hb + ((curveS W).a₁ * om W) * ha
      · apply X_pow_succ_dvd_of_derivative hR (by rw [map_sub, h0y, sub_self])
        refine ⟨om W * (3 * (x + x') * a + 2 * (curveS W).a₂ * a - (curveS W).a₁ * b), ?_⟩
        rw [map_sub, eD y, eD y', hy, hy']
        linear_combination (om W * (3 * (x + x') + 2 * (curveS W).a₂)) * ha
          - ((curveS W).a₁ * om W) * hb
  constructor
  · exact sub_eq_zero.mp (eq_zero_of_forall_X_pow_dvd fun n => (key n).1)
  · exact sub_eq_zero.mp (eq_zero_of_forall_X_pow_dvd fun n => (key n).2)

theorem chord_equation : ChordEquation.{u} := by
  intro R _ W xP yP xQ yQ t hP hQ ht
  rw [WeierstrassCurve.Affine.equation_iff] at hP hQ
  have hL : (yP - yQ) * t * (xP - xQ) = yP - yQ := by linear_combination (yP - yQ) * ht
  obtain ⟨hc1, hc0⟩ := chord_rel hP hQ ht hL
  generalize (yP - yQ) * t = L at hL hc1 hc0 ⊢
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.addX]
  linear_combination -(L ^ 2 + W.a₁ * L - W.a₂ - xP - xQ) * hc1 - hc0

theorem addition_addition : PlusPlus.{u} := by
  intro R _ W xP yP xQ yQ t hR hP hQ ht s hs
  obtain ⟨hDer, hConst, -, -, -, -⟩ := flowU R W
  obtain ⟨hFP, hxP0, hyP0⟩ := plusFlow R W xP yP hP
  have hPQ := chord_equation R W xP yP xQ yQ t hP hQ ht
  obtain ⟨hFS, hxS0, hyS0⟩ := plusFlow R W _ _ hPQ
  have hDC : ∀ r : R, D W (C r) = 0 := fun r => by
    rw [CurveSer.D_apply, derivative_C, mul_zero]
  have hQC : (curveS W).toAffine.Equation (C xQ) (C yQ) :=
    WeierstrassCurve.Affine.Equation.map (C : R →+* R⟦X⟧) hQ
  have hFT := flowTranslate _ (curveS W) (D W) (xPlus W xP yP) (yPlus W xP yP) (C xQ) (C yQ) s
    hDer hConst hFP hQC (hDC xQ) (hDC yQ) hs
  have hs0 : constantCoeff s = t := by
    have h := congrArg (constantCoeff (R := R)) hs
    rw [map_mul, map_sub, hxP0, constantCoeff_C, map_one] at h
    linear_combination t * h - constantCoeff s * ht
  refine flow_unique R W _ _ _ _ hR hFS hFT ?_ ?_
  · rw [hxS0]
    simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      map_add, map_sub, map_mul, map_pow, constantCoeff_C, hxP0, hyP0, hs0]
  · rw [hyS0]
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.addX, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      map_add, map_sub, map_neg, map_mul, map_pow, constantCoeff_C, hxP0, hyP0, hs0]

theorem addition_neg_y : PlusNegY.{u} := by
  intro R _ W xP yP _
  have hI : ISerSpec.{u} := iSerSpec
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨hi0, -, -, -, -, hy, -, -⟩ := hI R W
    have hv := Plus.inv_subst W xP hI
    have hn := Plus.nS_subst W xP yP hI
    have hxp := Plus.xPlus_subst W xP yP hI
    have hqr := CurveSer.iDen_mul_inv W
    have htv := Plus.tDen_mul_inv W xP
    rw [← Plus.subHom_apply _ hi0] at hv hn hxp hy ⊢
    have φX : Plus.subHom (iSer W) hi0 X = X * invOfUnit (iDen W) (-1) := Plus.subHom_X _ _
    rw [yPlus, map_sub, map_sub, map_sub, map_neg, map_mul, map_mul, map_mul, map_sub, map_mul,
      map_pow, map_pow, Plus.subHom_C, Plus.subHom_C, Plus.subHom_C, φX, hv, hn, hxp, hy]
    simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
    rw [yPlus]
    have hx' : xPlus W xP (W.toAffine.negY xP yP) = C xP
        + X * nS W xP (W.toAffine.negY xP yP) * invOfUnit (tDen W xP) 1 ^ 2 := rfl
    simp only [WeierstrassCurve.Affine.negY] at hx' ⊢
    rw [hx']
    simp only [map_sub, map_neg, map_mul]
    generalize nS W xP (-yP - W.a₁ * xP - W.a₃) = n'
    generalize invOfUnit (iDen W) (-1) = r at hqr
    generalize invOfUnit (tDen W xP) 1 = v at htv
    generalize iDen W = q at hqr
    rw [tDen] at htv
    linear_combination (yS W + C W.a₁ * X * xS W + C W.a₃ * X ^ 3 + C yP * X ^ 3) * n' * v ^ 3
        * ((q * r) ^ 5 + (q * r) ^ 4 + (q * r) ^ 3 + (q * r) ^ 2 + q * r + 1) * hqr
      + C W.a₁ * X * n' * v ^ 2 * htv
  · simp only [xPlus, tS, nS, WeierstrassCurve.Affine.negY, map_add, map_sub, map_neg, map_mul,
      map_pow, map_ofNat]
    ring
  · rw [xPlus, map_add, coeff_C, if_neg one_ne_zero, zero_add, mul_assoc, coeff_succ_X_mul,
      coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, Plus.nS_cc, Plus.inv_cc]
    ring

theorem expSeriesAdd : ExpAdd.{u} := by
  intro K _ _ W
  obtain ⟨l0, -, -, -⟩ := logSpec K W
  obtain ⟨e0, -, hle, -, -⟩ := expSpec K W
  have c0 : MvPowerSeries.constantCoeff (U₁ : MvPowerSeries (Fin 2) K) = 0 := by simp
  have c1 : MvPowerSeries.constantCoeff (U₂ : MvPowerSeries (Fin 2) K) = 0 := by simp
  have hU0 : HasSubst (U₁ : MvPowerSeries (Fin 2) K) := HasSubst.of_constantCoeff_zero c0
  have hU1 : HasSubst (U₂ : MvPowerSeries (Fin 2) K) := HasSubst.of_constantCoeff_zero c1
  have he : HasSubst (expSer W) := HasSubst.of_constantCoeff_zero' e0
  have ce0 : MvPowerSeries.constantCoeff ((expSer W).subst (U₁ : MvPowerSeries (Fin 2) K)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero c0 _ e0
  have ce1 : MvPowerSeries.constantCoeff ((expSer W).subst (U₂ : MvPowerSeries (Fin 2) K)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero c1 _ e0
  have hb : MvPowerSeries.HasSubst (![(expSer W).subst (U₁ : MvPowerSeries (Fin 2) K),
      (expSer W).subst (U₂ : MvPowerSeries (Fin 2) K)] : Fin 2 → MvPowerSeries (Fin 2) K) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by
      fin_cases s
      · exact ce0
      · exact ce1)
  have cl : MvPowerSeries.constantCoeff ((logSer W).subst (U₁ : MvPowerSeries (Fin 2) K)
      + (logSer W).subst (U₂ : MvPowerSeries (Fin 2) K)) = 0 := by
    rw [map_add, PowerSeries.constantCoeff_subst_eq_zero c0 _ l0,
      PowerSeries.constantCoeff_subst_eq_zero c1 _ l0, add_zero]
  have k0 : (logSer W).subst ((expSer W).subst (U₁ : MvPowerSeries (Fin 2) K)) = U₁ := by
    have key := subst_comp_subst_apply he hU0 (logSer W)
    rw [hle, subst_X hU0] at key
    exact key.symm
  have k1 : (logSer W).subst ((expSer W).subst (U₂ : MvPowerSeries (Fin 2) K)) = U₂ := by
    have key := subst_comp_subst_apply he hU1 (logSer W)
    rw [hle, subst_X hU1] at key
    exact key.symm
  conv_rhs => rw [(fglLog K W).2]
  rw [Fgl2.mvsubst_psubst (HasSubst.of_constantCoeff_zero cl) hb, MvPowerSeries.subst_add hb,
    Fgl2.mvsubst_psubst hU0 hb, Fgl2.mvsubst_psubst hU1 hb, MvPowerSeries.subst_X hb,
    MvPowerSeries.subst_X hb]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [k0, k1]

theorem plusZCleared_of (hZ : PlusZ.{u}) (hT : TInZ.{u}) : PlusZCleared.{u} := by
  intro K _ _ W xP yP hP
  obtain ⟨-, -, hlog⟩ := hZ K W xP yP hP
  have hT' := hT K W xP
  have hsh := (wpShape K W).1
  set P := wpReg W with hPdef
  set c : K := xP + W.b₂ / 12 with hc
  set T := (tS W xP).subst (expSer W) with hTdef
  set xp := (xPlus W xP yP).subst (expSer W) with hxp
  set xm := (xPlus W xP (W.toAffine.negY xP yP)).subst (expSer W) with hxm
  set f : K⟦X⟧ := 1 + X ^ 2 * (P - C c) with hf
  have hf0 : constantCoeff f = 1 := by simp [hf]
  set g : K⟦X⟧ := invOfUnit f 1 with hg
  have hfg : f * g = 1 := mul_invOfUnit _ _ (by rw [hf0, Units.val_one])
  have hTf : T * f = X ^ 2 := by rw [← hT', hf]; ring
  have hTg : T = X ^ 2 * g := by linear_combination g * hTf - T * hfg
  have hdf : X * derivative K f = 2 * (f - 1) + X ^ 3 * derivative K P := by
    rw [hf]
    simp only [map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow, derivative_X,
      derivative_C, Derivation.map_one_eq_zero, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  have hdg : derivative K g = -g ^ 2 * derivative K f := by
    have h := congrArg (derivative K) hfg
    rw [Derivation.leibniz, Derivation.map_one_eq_zero, smul_eq_mul, smul_eq_mul] at h
    linear_combination g * h - derivative K g * hfg
  have hz : (toL X : LaurentSeries K) * uPow (-1) = 1 := Plus.toL_X_mul
  have hxZ : xZ W = uPow (-2) + toL P - HahnSeries.C (W.b₂ / 12) := by
    rw [← hsh, wpL]; ring

  have hdwp : dL (wpL W) = uPow (-1) ^ 3 * (toL X * toL (derivative K f) - 2 * toL f) := by
    have h1 : toL X * toL (derivative K f) = 2 * (toL f - 1) + toL X ^ 3 * toL (derivative K P) := by
      rw [← map_mul, hdf]
      simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]
    rw [hsh, map_add, dL_uPow, dL_toL, h1]
    have e3 : (uPow (-2 - 1) : LaurentSeries K) = uPow (-1) ^ 3 := by
      rw [← Plus.uPow_neg_three]; norm_num
    rw [e3]
    have e2 : (HahnSeries.C (((-2 : ℤ) : K)) : LaurentSeries K) = -2 := by
      push_cast
      rw [map_neg, map_ofNat]
    rw [e2]
    linear_combination (-toL (derivative K P)
      * ((toL X * uPow (-1)) ^ 2 + toL X * uPow (-1) + 1)) * hz
  have hprod : toL T * dL (wpL W) = toL (g * derivative K f) - 2 * uPow (-1) := by
    have hfg' : toL f * toL g = 1 := by rw [← map_mul, hfg, map_one]
    rw [hdwp, hTg, map_mul, map_mul, map_pow]
    linear_combination (toL g * toL (derivative K f) * ((toL X * uPow (-1)) ^ 2
        + toL X * uPow (-1) + 1) - 2 * toL g * toL f * uPow (-1) * (toL X * uPow (-1) + 1)) * hz
      - 2 * uPow (-1) * hfg'
  rw [hprod, map_sub, dL_toL, dL_mul, dL_uPow, hxZ] at hlog
  have e2' : (uPow (-1 - 1) : LaurentSeries K) = uPow (-2) := by norm_num
  have e1 : (HahnSeries.C (((-1 : ℤ) : K)) : LaurentSeries K) = -1 := by
    push_cast
    rw [map_neg, map_one]
  have d2 : dL (2 : LaurentSeries K) = 0 := by
    rw [← map_ofNat (HahnSeries.C : K →+* LaurentSeries K) 2, dL_C]
  rw [e2', e1, d2] at hlog
  have hmain : derivative K (g * derivative K f) = 2 * P - (xp + C (W.b₂ / 12))
      - (xm + C (W.b₂ / 12)) := by
    apply toL_injective
    simp only [map_add, map_sub, map_mul, map_ofNat, toL_C]
    linear_combination hlog
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hdg] at hmain
  rw [← hmain]
  linear_combination (-(derivative K (derivative K f)) * f
    + derivative K f ^ 2 * (f * g + 1)) * hfg

end Formalism.L2.Th1.A
