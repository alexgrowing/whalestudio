import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementI
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowTwoTorsionWp

open PowerSeries

universe u

noncomputable section

namespace Formalism.L2.Th1.A

theorem two_torsion_unit : TwoTorsionU.{u} := by
  intro R _ W xT yT hT h2
  obtain ⟨hDer, hConst, hC, hD⟩ := dLSpec R W
  have hx := (plusChord R W xT yT hT).1
  have h2' : 2 * (HahnSeries.C yT : LaurentSeries R) + (curveL W).a₁ * HahnSeries.C xT
      + (curveL W).a₃ = 0 := by
    have h := congrArg (HahnSeries.C : R →+* LaurentSeries R) h2
    simpa only [map_add, map_mul, map_ofNat, map_zero, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₃] using h
  obtain ⟨a, b, c⟩ := flowTwoTorsion _ (curveL W) (DL W) (xL W) (yL W) (HahnSeries.C xT)
    (HahnSeries.C yT) (toL (tS W xT)) hDer hConst (flowL R W).1 (Plus.equation_C W hT) (hC xT)
    (hC yT) h2' (Plus.toL_tS_mul W xT)
  rw [hD] at b c
  rw [hD] at c
  refine ⟨?_, ?_, ?_⟩
  · apply toL_injective
    rw [hx, slopeL, a]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, toL_C, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄]
  · apply toL_injective
    rw [map_pow, b]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, toL_C, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄, WeierstrassCurve.map_b₂]
  · apply toL_injective
    rw [c]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, toL_C, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄, WeierstrassCurve.map_b₂]

namespace Two

variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)

theorem e0 : constantCoeff (expSer W) = 0 := by
  unfold expSer compInv
  split_ifs with h
  · exact h.choose_spec.1
  · simp

theorem he : HasSubst (expSer W) := PowerSeries.HasSubst.of_constantCoeff_zero' (e0 W)

theorem toL_exp_ne : toL (expSer W) ≠ 0 := by
  intro h
  have h1 := (expSpec K W).2.1
  rw [(map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective).mp h, map_zero] at h1
  exact zero_ne_one h1

theorem exp_mul_inv : toL (expSer W) * (toL (expSer W))⁻¹ = 1 := mul_inv_cancel₀ (toL_exp_ne W)

theorem uPow_mul_sq : (uPow (-2) : LaurentSeries K) * toL X ^ 2 = 1 := by
  simp only [uPow]
  rw [← map_pow, HahnSeries.ofPowerSeries_X_pow, HahnSeries.single_mul_single]
  norm_num [HahnSeries.single_zero_one]

theorem tS_mul (xP : K) :
    toL ((tS W xP).subst (expSer W)) * (xZ W - HahnSeries.C xP) = 1 := by
  have hne := toL_exp_ne W
  have hc : constantCoeff (tDen W xP) = 1 := by
    simp [tDen, xS, PowerSeries.constantCoeff_invOfUnit]
  have hm : tDen W xP * invOfUnit (tDen W xP) 1 = 1 :=
    PowerSeries.mul_invOfUnit _ _ (by simpa using hc)
  have hC : (C xP : K⟦X⟧).subst (expSer W) = C xP := by
    rw [← PowerSeries.coe_substAlgHom (he W)]
    exact (PowerSeries.substAlgHom (he W)).commutes xP
  have ht : (xS W).subst (expSer W) = (tDen W xP).subst (expSer W) + C xP * expSer W ^ 2 := by
    rw [tDen, ← PowerSeries.coe_substAlgHom (he W), map_sub, map_mul, map_pow,
      PowerSeries.coe_substAlgHom, PowerSeries.subst_X (he W), hC]
    ring
  have h1 : toL ((tDen W xP).subst (expSer W)) * toL ((invOfUnit (tDen W xP) 1).subst (expSer W)) = 1 := by
    rw [← map_mul, ← PowerSeries.coe_substAlgHom (he W), ← map_mul, hm, map_one, map_one]
  have hE : toL (expSer W) * (toL (expSer W))⁻¹ = 1 := mul_inv_cancel₀ hne
  have hs : (tS W xP).subst (expSer W) = expSer W ^ 2 * (invOfUnit (tDen W xP) 1).subst (expSer W) := by
    rw [tS, ← PowerSeries.coe_substAlgHom (he W), map_mul, map_pow, PowerSeries.coe_substAlgHom,
      PowerSeries.subst_X (he W)]
  rw [hs, xZ, ht]
  simp only [map_add, map_mul, map_pow, HahnSeries.ofPowerSeries_C]
  linear_combination (toL (expSer W) * (toL (expSer W))⁻¹ + 1) * (toL ((invOfUnit (tDen W xP) 1).subst (expSer W)) * toL ((tDen W xP).subst (expSer W)) + HahnSeries.C xP * toL ((invOfUnit (tDen W xP) 1).subst (expSer W)) * toL (expSer W) ^ 2) * hE + h1

theorem chordZ {xP yP : K} (hP : W.toAffine.Equation xP yP) :
    toL ((xPlus W xP yP).subst (expSer W)) = (curveL W).toAffine.addX (xZ W) (HahnSeries.C xP)
      ((yZ W - HahnSeries.C yP) * toL ((tS W xP).subst (expSer W))) := by
  obtain ⟨hX, -⟩ := chordRegular _ (curveL W) (xZ W) (yZ W) (HahnSeries.C xP)
    (HahnSeries.C yP) (toL ((tS W xP).subst (expSer W))) (flowZ K W).1.1 (Plus.equation_C W hP)
    (tS_mul W xP)
  have h := exp_mul_inv W
  rw [hX, xZ, yZ]
  simp only [← Wp.sig_apply (he W)]
  simp only [xPlus, nS, tS, map_add, map_sub, map_mul, map_pow, map_ofNat, Wp.sig_C, Wp.sig_X,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  generalize Wp.sig (he W) (invOfUnit (tDen W xP) 1) = v
  generalize Wp.sig (he W) (xS W) = xs
  generalize Wp.sig (he W) (yS W) = ys
  generalize (toL (expSer W))⁻¹ = q at h ⊢
  generalize toL (expSer W) = E at h ⊢
  linear_combination (-(HahnSeries.C W.a₄ - HahnSeries.C W.a₁ * HahnSeries.C yP
        + 2 * HahnSeries.C W.a₂ * HahnSeries.C xP + 3 * HahnSeries.C xP ^ 2) * xs * v ^ 2
          * E ^ 2 * (E * q + 1)
      + (2 * HahnSeries.C yP + HahnSeries.C W.a₁ * HahnSeries.C xP + HahnSeries.C W.a₃) * ys
          * v ^ 2 * E * ((E * q) ^ 2 + E * q + 1)) * h

theorem isFlow_subst {a b : K⟦X⟧} (h : IsFlow (curveS W) (D W) a b) :
    IsFlow (curveS W) (derivative K) (a.subst (expSer W)) (b.subst (expSer W)) := by
  obtain ⟨hE, hDa, hDb⟩ := h
  have hφ : ∀ f : K⟦X⟧, f.subst (expSer W) = PowerSeries.substAlgHom (he W) f := fun f => by
    rw [PowerSeries.coe_substAlgHom]
  have hC : ∀ c : K, PowerSeries.substAlgHom (he W) (C c) = C c := fun c =>
    (PowerSeries.substAlgHom (he W)).commutes c
  refine ⟨?_, ?_, ?_⟩
  · rw [WeierstrassCurve.Affine.equation_iff] at hE ⊢
    have h2 := congrArg (PowerSeries.substAlgHom (he W)) hE
    simp only [map_add, map_mul, map_pow, curveS, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, hC] at h2 ⊢
    rw [hφ, hφ]
    exact h2
  · rw [chainZ K W, hDa]
    simp only [hφ, map_add, map_mul, map_ofNat, curveS, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, hC]
  · rw [chainZ K W, hDb]
    simp only [hφ, map_add, map_sub, map_mul, map_pow, map_ofNat, curveS, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄, hC]

theorem subst_tS (xP : K) : (tS W xP).subst (expSer W)
    = expSer W ^ 2 * (invOfUnit (tDen W xP) 1).subst (expSer W) := by
  rw [tS, ← PowerSeries.coe_substAlgHom (he W), map_mul, map_pow, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X (he W)]

private theorem cc_subst_lemma {R : Type*} [CommRing R] {e : R⟦X⟧} (he : HasSubst e)
    (he0 : constantCoeff e = 0) (f : R⟦X⟧) : constantCoeff (f.subst e) = constantCoeff f := by
  have hC : (C (constantCoeff f) : R⟦X⟧).subst e = C (constantCoeff f) := by
    rw [← PowerSeries.coe_substAlgHom he]
    exact (PowerSeries.substAlgHom he).commutes _
  conv_lhs => rw [PowerSeries.eq_shift_mul_X_add_const f]
  rw [← PowerSeries.coe_substAlgHom he, map_add, map_mul, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X he, hC, map_add, map_mul, he0, mul_zero, zero_add, PowerSeries.constantCoeff_C]

theorem inv_subst_cc (xP : K) :
    constantCoeff ((invOfUnit (tDen W xP) 1).subst (expSer W)) = 1 := by
  have hc : constantCoeff (tDen W xP) = 1 := by
    simp [tDen, xS, PowerSeries.constantCoeff_invOfUnit]
  have hm : tDen W xP * invOfUnit (tDen W xP) 1 = 1 :=
    PowerSeries.mul_invOfUnit _ _ (by simpa using hc)
  have h1 : (tDen W xP).subst (expSer W) * (invOfUnit (tDen W xP) 1).subst (expSer W) = 1 := by
    rw [← PowerSeries.coe_substAlgHom (he W), ← map_mul, hm, map_one]
  have h2 := congrArg constantCoeff h1
  rw [map_mul, map_one, cc_subst_lemma (he W) (e0 W) (tDen W xP), hc, one_mul] at h2
  exact h2

theorem sq_dvd_tS (xP : K) : X ^ 2 ∣ (tS W xP).subst (expSer W) := by
  rw [subst_tS]
  exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.mpr (e0 W)) 2) _

theorem coeff_two_tS (xP : K) : coeff 2 ((tS W xP).subst (expSer W)) = 1 := by
  obtain ⟨e1, he1⟩ : X ∣ expSer W := PowerSeries.X_dvd_iff.mpr (e0 W)
  have hc1 : constantCoeff e1 = 1 := by
    have h1 := (expSpec K W).2.1
    rw [he1, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply] at h1
    exact h1
  rw [subst_tS]
  have hg := inv_subst_cc W xP
  generalize (invOfUnit (tDen W xP) 1).subst (expSer W) = g at hg ⊢
  rw [he1, mul_pow, mul_assoc, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, hc1, hg]
  norm_num

theorem tS_even (xP : K) :
    PowerSeries.subst (-X : K⟦X⟧) ((tS W xP).subst (expSer W) : K⟦X⟧)
      = (tS W xP).subst (expSer W) := by
  have hX : HasSubst (-X : K⟦X⟧) := HasSubst.of_constantCoeff_zero' (by simp)
  have hi : HasSubst (iSer W) := HasSubst.of_constantCoeff_zero' (iSerSpec K W).1
  have k1 := subst_comp_subst_apply (he W) hX (tS W xP)
  have k2 := subst_comp_subst_apply hi (he W) (tS W xP)
  rw [(tSpec K W xP).2.2.2.2.2] at k2
  rw [k1, (logNeg K W).2, ← k2]

end Two

open Two

theorem addition_integral : PlusZ.{u} := by
  intro K _ _ W xP yP hP
  refine ⟨isFlow_subst W (plusFlow K W xP yP hP).1, tS_mul W xP, ?_⟩
  have h := flowLogDeriv _ (curveL W) dL (xZ W) (yZ W) (HahnSeries.C xP) (HahnSeries.C yP)
    (toL ((tS W xP).subst (expSer W))) Wp.isDer_dL' (Wp.constCurve_dL W) (flowZ K W).1
    (Plus.equation_C W hP) (dL_C _) (dL_C _) (tS_mul W xP)
  rw [WeierstrassCurve.Affine.map_negY] at h
  have hw : dL (wpL W) = dL (xZ W) := by rw [wpL, map_add, dL_C, add_zero]
  rw [hw, chordZ W hP, chordZ W ((WeierstrassCurve.Affine.equation_neg xP yP).2 hP), h]

theorem two_torsion_integral : TwoTorsionZ.{u} := by
  intro K _ _ W xT yT hT h2 e₁ kap w₁
  obtain ⟨he₁⟩ : Nonempty (e₁ = xT + W.b₂ / 12) := ⟨rfl⟩
  obtain ⟨hkap⟩ : Nonempty (kap = 3 * e₁ ^ 2 - g₂ W / 4) := ⟨rfl⟩
  obtain ⟨hw₁⟩ : Nonempty (w₁ = (tS W xT).subst (expSer W)) := ⟨rfl⟩
  clear_value w₁ kap e₁
  have hinj : Function.Injective (HahnSeries.C : K →+* LaurentSeries K) := HahnSeries.C_injective
  have cE : (HahnSeries.C e₁ : LaurentSeries K) = HahnSeries.C xT + HahnSeries.C (W.b₂ / 12) := by
    rw [he₁, map_add]
  have h6 : IsUnit (6 : LaurentSeries K) := by
    have h := (IsUnit.mk0 (6 : K) (by norm_num)).map (HahnSeries.C : K →+* LaurentSeries K)
    rwa [map_ofNat] at h
  have hb : 12 * (HahnSeries.C (W.b₂ / 12) : LaurentSeries K) = (curveL W).b₂ := by
    rw [WeierstrassCurve.map_b₂, ← map_ofNat (HahnSeries.C : K →+* LaurentSeries K) 12, ← map_mul]
    congr 1
    field_simp
  have hg2 : 12 * (HahnSeries.C (g₂ W) : LaurentSeries K) = (curveL W).c₄ := by
    rw [WeierstrassCurve.map_c₄, ← map_ofNat (HahnSeries.C : K →+* LaurentSeries K) 12, ← map_mul]
    congr 1
    rw [g₂]
    field_simp
  have hg3 : 216 * (HahnSeries.C (g₃ W) : LaurentSeries K) = (curveL W).c₆ := by
    rw [WeierstrassCurve.map_c₆, ← map_ofNat (HahnSeries.C : K →+* LaurentSeries K) 216, ← map_mul]
    congr 1
    rw [g₃]
    field_simp
  have hk : 4 * (HahnSeries.C kap : LaurentSeries K)
      = 12 * (HahnSeries.C xT + HahnSeries.C (W.b₂ / 12)) ^ 2 - HahnSeries.C (g₂ W) := by
    have h : 4 * kap = 12 * e₁ ^ 2 - g₂ W := by rw [hkap]; ring
    have h' := congrArg (HahnSeries.C : K →+* LaurentSeries K) h
    rw [← cE]
    simpa only [map_sub, map_mul, map_pow, map_ofNat] using h'
  have h2' : 2 * (HahnSeries.C yT : LaurentSeries K) + (curveL W).a₁ * HahnSeries.C xT
      + (curveL W).a₃ = 0 := by
    have h := congrArg (HahnSeries.C : K →+* LaurentSeries K) h2
    simpa only [map_add, map_mul, map_ofNat, map_zero, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₃] using h
  have ht : toL w₁ * (xZ W - HahnSeries.C xT) = 1 := by rw [hw₁]; exact tS_mul W xT
  obtain ⟨p1, p2, -, p4, p5⟩ := flowTwoTorsionWp _ (curveL W) dL (xZ W) (yZ W) (HahnSeries.C xT)
    (HahnSeries.C yT) (toL w₁) (HahnSeries.C (W.b₂ / 12)) (HahnSeries.C (g₂ W))
    (HahnSeries.C (g₃ W)) (HahnSeries.C kap) Wp.isDer_dL' (Wp.constCurve_dL W) (flowZ K W).1
    (Plus.equation_C W hT) (dL_C _) (dL_C _) h2' ht h6 hb hg2 hg3 hk
  obtain ⟨-, -, s3⟩ := flowTwoTorsion _ (curveL W) dL (xZ W) (yZ W) (HahnSeries.C xT)
    (HahnSeries.C yT) (toL w₁) Wp.isDer_dL' (Wp.constCurve_dL W) (flowZ K W).1
    (Plus.equation_C W hT) (dL_C _) (dL_C _) h2' ht
  rw [← cE] at p1 p4 p5
  rw [← p2, ← hb, dL_toL, dL_toL] at s3
  rw [dL_toL] at p4 p5
  have q1 : 4 * e₁ ^ 3 - g₂ W * e₁ - g₃ W = 0 := by
    apply hinj
    simpa only [map_sub, map_mul, map_pow, map_ofNat, map_zero] using p1
  have q3 : kap = 3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT := by
    apply hinj
    simpa only [map_add, map_sub, map_mul, map_pow, map_ofNat, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄] using p2
  refine ⟨q1, ?_, q3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hg3' : g₃ W = 4 * e₁ ^ 3 - g₂ W * e₁ := by linear_combination -q1
    have h4 : (4 : Polynomial K) * Polynomial.C (g₂ W / 4) = Polynomial.C (g₂ W) := by
      rw [← map_ofNat (Polynomial.C : K →+* Polynomial K) 4, ← map_mul]
      congr 1
      field_simp
    rw [hg3']
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    linear_combination (Polynomial.X - Polynomial.C e₁) * h4
  · rw [wpL, cE]
    linear_combination ht
  · rw [hw₁]; exact sq_dvd_tS W xT
  · rw [hw₁]; exact coeff_two_tS W xT
  · rw [hw₁]; exact tS_even W xT
  · apply toL_injective
    simpa only [map_add, map_mul, map_pow, map_one, map_ofNat, toL_C] using p4
  · apply toL_injective
    simp only [map_add, map_mul, map_pow, map_ofNat, toL_C]
    rw [s3, cE]
    ring
  · rw [(two_torsion_unit K W xT yT hT h2).1, ← q3, subst_add (he W), subst_mul (he W), ← hw₁,
      ← ISer.subHom_apply _ (e0 W), ← ISer.subHom_apply _ (e0 W), ISer.subHom_C, ISer.subHom_C,
      he₁, map_add]
    ring
  · intro e₂ e₃ hf
    have v0 := congrArg (Polynomial.eval 0) hf
    have v1 := congrArg (Polynomial.eval 1) hf
    have vm := congrArg (Polynomial.eval (-1)) hf
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_ofNat] at v0 v1 vm
    have s1 : e₁ + e₂ + e₃ = 0 := by linear_combination (1 / 8) * (v1 + vm - 2 * v0)
    have s2 : 4 * (e₁ * e₂ + e₁ * e₃ + e₂ * e₃) = -g₂ W := by
      linear_combination (-1 / 2) * (v1 - vm)
    refine ⟨by rw [hkap]; linear_combination 2 * e₁ * s1 - (1 / 4) * s2, ?_⟩
    have p := p5 (HahnSeries.C e₂) (HahnSeries.C e₃)
      (by rw [← map_add, ← map_add, s1, map_zero])
      (by
        have h := congrArg (HahnSeries.C : K →+* LaurentSeries K) s2
        simpa only [map_add, map_mul, map_neg, map_ofNat] using h)
    apply toL_injective
    simpa only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, toL_C] using p

namespace Two

variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)

theorem wpInZ (hS : WpShape.{u}) : expSer W ^ 2 * (1 + X ^ 2 * wpReg W)
    = X ^ 2 * ((xS W).subst (expSer W) + C (W.b₂ / 12) * expSer W ^ 2) := by
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)
  have hw := (hS K W).1
  unfold wpL xZ at hw
  have hP : (uPow (-2) : LaurentSeries K) * toL X ^ 2 = 1 := uPow_mul_sq
  have hE1 : toL (expSer W) * (toL (expSer W))⁻¹ = 1 := mul_inv_cancel₀ (toL_exp_ne W)
  simp only [map_mul, map_pow, map_add, map_one, HahnSeries.ofPowerSeries_C]
  linear_combination (-(toL X ^ 2 * toL (expSer W) ^ 2)) * hw + (-(toL (expSer W) ^ 2)) * hP
    + (toL X ^ 2 * toL ((xS W).subst (expSer W)) * (toL (expSer W) * (toL (expSer W))⁻¹ + 1)) * hE1

end Two

theorem wpInU_of (hS : WpShape.{u}) : WpInU.{u} := by
  intro K _ _ W
  have h := Two.wpInZ W hS
  have hl : PowerSeries.HasSubst (logSer W) := PowerSeries.HasSubst.of_constantCoeff_zero' (logSpec K W).1
  have hel : (expSer W).subst (logSer W) = X := (expSpec K W).2.2.2.1
  have hself : ∀ f : K⟦X⟧, f.subst (X : K⟦X⟧) = f := fun f => by
    show MvPowerSeries.subst (fun _ => (PowerSeries.X : K⟦X⟧)) f = f
    have e : (fun _ : Unit => (PowerSeries.X : K⟦X⟧)) = MvPowerSeries.X := funext fun _ => rfl
    rw [e, MvPowerSeries.subst_self]
    rfl
  have h2 := congrArg (PowerSeries.substAlgHom hl) h
  simp only [map_mul, map_pow, map_add, map_one, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hl] at h2
  have e1 : PowerSeries.substAlgHom hl (expSer W) = X := by rw [PowerSeries.coe_substAlgHom]; exact hel
  have e2 : PowerSeries.substAlgHom hl (wpReg W) = (wpReg W).subst (logSer W) := by
    rw [PowerSeries.coe_substAlgHom]
  have e3 : PowerSeries.substAlgHom hl ((xS W).subst (expSer W)) = xS W := by
    rw [PowerSeries.coe_substAlgHom, PowerSeries.subst_comp_subst_apply (Two.he W) hl, hel, hself]
  have e4 : PowerSeries.substAlgHom hl (C (W.b₂ / 12)) = C (W.b₂ / 12) :=
    (PowerSeries.substAlgHom hl).commutes _
  have e3' : PowerSeries.subst (logSer W : K⟦X⟧) (PowerSeries.subst (expSer W : K⟦X⟧) (xS W)) = xS W := by
    rw [PowerSeries.subst_comp_subst_apply (Two.he W) hl, hel, hself]
  have e4' : PowerSeries.subst (logSer W : K⟦X⟧) (C (W.b₂ / 12) : K⟦X⟧) = C (W.b₂ / 12) := by
    rw [← PowerSeries.coe_substAlgHom hl]
    exact (PowerSeries.substAlgHom hl).commutes _
  simp only [e1, e2, e3, e4, hel, e3', e4'] at h2
  exact h2

theorem tInZ_of (hS : WpShape.{u}) : TInZ.{u} := by
  intro K _ _ W xP
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)
  have h1 := Two.tS_mul W xP
  have hw := (hS K W).1
  unfold wpL at hw
  have hP : (uPow (-2) : LaurentSeries K) * toL X ^ 2 = 1 := Two.uPow_mul_sq
  simp only [map_mul, map_sub, map_add, map_one, map_pow, HahnSeries.ofPowerSeries_C]
  linear_combination (-(toL ((tS W xP).subst (expSer W)) * toL X ^ 2)) * hw + toL X ^ 2 * h1
    + (-(toL ((tS W xP).subst (expSer W)))) * hP

theorem logarithm_coeff : LogCoeff.{u} := by
  intro K _ _ W n
  simp only [logSer, integ, PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]
  have hn : ((n + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  field_simp

end Formalism.L2.Th1.A
