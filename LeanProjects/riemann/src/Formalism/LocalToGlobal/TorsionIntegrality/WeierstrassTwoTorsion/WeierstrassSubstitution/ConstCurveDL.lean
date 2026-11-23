import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementZ
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementT
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.FlowBasic
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.Laurent
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.CurveSer

open PowerSeries

universe u

noncomputable section

namespace Formalism.L2.Th1.A

namespace Wp

variable {K : Type u} [Field K]

def sig {e : K⟦X⟧} (he : HasSubst e) : K⟦X⟧ →+* LaurentSeries K :=
  toL.comp (substAlgHom he : K⟦X⟧ →ₐ[K] K⟦X⟧).toRingHom

theorem sig_apply {e : K⟦X⟧} (he : HasSubst e) (f : K⟦X⟧) : sig he f = toL (f.subst e) := by
  simp [sig, PowerSeries.coe_substAlgHom]

theorem sig_X {e : K⟦X⟧} (he : HasSubst e) : sig he X = toL e := by
  rw [sig_apply, PowerSeries.subst_X he]

theorem sig_C {e : K⟦X⟧} (he : HasSubst e) (r : K) : sig he (C r) = HahnSeries.C r := by
  have h : (C r : K⟦X⟧).subst e = C r := by
    rw [← PowerSeries.coe_substAlgHom he]
    exact (PowerSeries.substAlgHom he).commutes r
  rw [sig_apply, h, HahnSeries.ofPowerSeries_C]

theorem isDer_dL' : IsDer (dL : LaurentSeries K → LaurentSeries K) := isDer_dL

theorem constCurve_dL (W : WeierstrassCurve K) : ConstCurve dL (curveL W) := by
  have h : ∀ c : K, dL (HahnSeries.C c : LaurentSeries K) = 0 := by
    intro c
    ext n
    simp [dL, HahnSeries.C_apply, HahnSeries.coeff_single]
  exact ⟨h _, h _, h _, h _, h _⟩

variable (W : WeierstrassCurve K) {e : K⟦X⟧} (he : HasSubst e)

theorem fwAt_sig : fwAt (curveL W) (sig he X) (sig he (wSer W)) = sig he (fw W) := by
  simp only [fwAt, fw, map_sub, map_mul, map_pow, map_one, map_ofNat, sig_C,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]

theorem fuAt_sig : fuAt (curveL W) (sig he X) (sig he (wSer W)) = sig he (fu W) := by
  simp only [fuAt, fu, map_add, map_mul, map_pow, map_ofNat, sig_C,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄]

theorem wEq_sig : WEq (curveL W) (sig he X) (sig he (wSer W)) := by
  have hw : wSer W = X ^ 3 + C W.a₁ * X * wSer W + C W.a₂ * X ^ 2 * wSer W + C W.a₃ * wSer W ^ 2
      + C W.a₄ * X * wSer W ^ 2 + C W.a₆ * wSer W ^ 3 :=
    (Formalism.ELL.wSeriesUnique K W).choose_spec.1.2
  have h := congrArg (sig he) hw
  simp only [map_add, map_mul, map_pow, sig_C] at h
  simp only [WEq, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  exact h

theorem isFlowUW_sig (hc : ∀ f : K⟦X⟧, derivative K (f.subst e) = (D W f).subst e) :
    IsFlowUW (curveL W) dL (sig he X) (sig he (wSer W)) := by
  have hw : wSer W = X ^ 3 + C W.a₁ * X * wSer W + C W.a₂ * X ^ 2 * wSer W + C W.a₃ * wSer W ^ 2
      + C W.a₄ * X * wSer W ^ 2 + C W.a₆ * wSer W ^ 3 :=
    (Formalism.ELL.wSeriesUnique K W).choose_spec.1.2
  have hd := congrArg (derivative K) hw
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, PowerSeries.derivative_C,
    PowerSeries.derivative_X, smul_eq_mul, nsmul_eq_mul] at hd
  have hDw : D W (wSer W) = fu W := by
    rw [D, Derivation.smul_apply, smul_eq_mul, fw, fu]
    linear_combination hd
  have hDX : D W X = fw W := by
    rw [D, Derivation.smul_apply, smul_eq_mul, PowerSeries.derivative_X, mul_one]
  refine ⟨wEq_sig W he, ?_, ?_⟩
  · have h2 : dL (sig he X) = sig he (fw W) := by
      have h1 := hc X
      rw [PowerSeries.subst_X he, hDX] at h1
      rw [sig_X, sig_apply, dL_toL, h1]
    rw [h2, fwAt_sig]
  · have h2 : dL (sig he (wSer W)) = sig he (fu W) := by
      rw [sig_apply, sig_apply, dL_toL, hc (wSer W), hDw]
    rw [h2, fuAt_sig]

theorem inv_mul_sig (hne : toL e ≠ 0) :
    (toL e)⁻¹ ^ 3 * sig he (xS W) * sig he (wSer W) = 1 := by
  have h1 : sig he (wU W) * sig he (xS W) = 1 := by rw [← map_mul, CurveSer.wU_mul_xS, map_one]
  have h2 : (toL e)⁻¹ * toL e = 1 := inv_mul_cancel₀ hne
  rw [CurveSer.wSer_eq, map_mul, map_pow, sig_X]
  calc (toL e)⁻¹ ^ 3 * sig he (xS W) * (toL e ^ 3 * sig he (wU W))
      = ((toL e)⁻¹ * toL e) ^ 3 * (sig he (wU W) * sig he (xS W)) := by ring
    _ = 1 := by rw [h1, h2, one_pow, one_mul]

include he in
theorem isFlow_sig (hc : ∀ f : K⟦X⟧, derivative K (f.subst e) = (D W f).subst e)
    (hne : toL e ≠ 0) :
    IsFlow (curveL W) dL ((toL e)⁻¹ ^ 2 * toL ((xS W).subst e))
      ((toL e)⁻¹ ^ 3 * toL ((yS W).subst e)) := by
  have h := chartFlowToFlow _ (curveL W) dL (sig he X) (sig he (wSer W))
    ((toL e)⁻¹ ^ 3 * sig he (xS W)) isDer_dL' (isFlowUW_sig W he hc) (inv_mul_sig W he hne)
  have h2 : (toL e)⁻¹ * toL e = 1 := inv_mul_cancel₀ hne
  have hx : sig he X * ((toL e)⁻¹ ^ 3 * sig he (xS W)) = (toL e)⁻¹ ^ 2 * toL ((xS W).subst e) := by
    rw [sig_X, sig_apply]
    linear_combination (toL e)⁻¹ ^ 2 * toL ((xS W).subst e) * h2
  have hy : -((toL e)⁻¹ ^ 3 * sig he (xS W)) = (toL e)⁻¹ ^ 3 * toL ((yS W).subst e) := by
    rw [← sig_apply he (yS W), yS, map_neg, mul_neg]
  rwa [hx, hy] at h

include he in
theorem mul_yZ_sig (hne : toL e ≠ 0) :
    toL e * ((toL e)⁻¹ ^ 3 * toL ((yS W).subst e)) = -((toL e)⁻¹ ^ 2 * toL ((xS W).subst e)) := by
  have hy : (yS W).subst e = -((xS W).subst e) := by
    rw [yS, ← PowerSeries.coe_substAlgHom he, map_neg]
  rw [hy, map_neg]
  have ht : toL e * (toL e)⁻¹ = 1 := mul_inv_cancel₀ hne
  calc toL e * ((toL e)⁻¹ ^ 3 * -toL ((xS W).subst e))
      = -((toL e * (toL e)⁻¹) * ((toL e)⁻¹ ^ 2 * toL ((xS W).subst e))) := by ring
    _ = -((toL e)⁻¹ ^ 2 * toL ((xS W).subst e)) := by rw [ht, one_mul]

end Wp

open Wp

theorem flowZ_of (hE : ExpSpec.{u}) (hC : ChainZ.{u}) : FlowZ.{u} := by
  intro K _ _ W
  obtain ⟨h0, h1, -, -, -⟩ := hE K W
  have he : HasSubst (expSer W) := HasSubst.of_constantCoeff_zero' h0
  have inj : Function.Injective (toL : K⟦X⟧ →+* LaurentSeries K) := HahnSeries.ofPowerSeries_injective
  have hne : toL (expSer W) ≠ 0 := by
    intro h
    have h' : expSer W = 0 := inj (by rw [h, map_zero])
    rw [h', map_zero] at h1
    exact zero_ne_one h1
  exact ⟨Wp.isFlow_sig W he (hC K W) hne, Wp.mul_yZ_sig W he hne⟩

theorem wpODE_of (hE : ExpSpec.{u}) (hC : ChainZ.{u}) : WpODE.{u} := by
  intro K _ _ W
  have hF := (flowZ_of hE hC K W).1
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
  obtain ⟨h1, h2, h3⟩ := flowWeierstrassForm _ (curveL W) dL (xZ W) (yZ W) (HahnSeries.C (W.b₂ / 12))
    (HahnSeries.C (g₂ W)) (HahnSeries.C (g₃ W)) isDer_dL' (constCurve_dL W) hF h6 hb hg2 hg3
  refine ⟨?_, h2, ?_⟩
  · simpa only [wpL, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃] using h1
  · have hh : (HahnSeries.C (1 / 2 : K) : LaurentSeries K) * 2 = 1 := by
      rw [← map_ofNat (HahnSeries.C : K →+* LaurentSeries K) 2, ← map_mul, ← map_one HahnSeries.C]
      congr 1
      norm_num
    have hg : (HahnSeries.C (g₂ W / 2) : LaurentSeries K)
        = HahnSeries.C (1 / 2 : K) * HahnSeries.C (g₂ W) := by
      rw [← map_mul]
      congr 1
      ring
    rw [hg]
    change 2 * dL (dL (wpL W)) = 12 * wpL W ^ 2 - HahnSeries.C (g₂ W) at h3
    linear_combination HahnSeries.C (1 / 2 : K) * h3 - (dL (dL (wpL W)) - 6 * wpL W ^ 2) * hh

end Formalism.L2.Th1.A
