import Development.WeilBound.CoreStatements.CentralCharts.TraceMulReNonneg
import Development.WeilBound.CoreStatements.CentralCharts.ContDiffAtLogNorm

noncomputable section

namespace AnalyticReference.An.H

open ReciprocityTheory.AnForm Filter Topology Matrix
open scoped ComplexOrder MatrixOrder

variable {n k r : ℕ}

theorem posDef_ofReal {Y : Matrix (Fin k) (Fin k) ℝ} (hY : Y.PosDef) : (Y.map Complex.ofReal).PosDef := by
  have h0 : 0 ≤ Y := hY.posSemidef.nonneg
  have h1 : (CFC.sqrt Y).PosSemidef := (CFC.sqrt_nonneg Y).posSemidef
  have h2 : Y = (CFC.sqrt Y)ᴴ * CFC.sqrt Y := by rw [h1.1.eq, CFC.sqrt_mul_sqrt_self Y h0]
  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin k) (Fin k) ℝ, Y = Sᴴ * S := ⟨_, h2⟩
  have h3 : Y.map Complex.ofReal = (S.map Complex.ofReal)ᴴ * S.map Complex.ofReal := by
    rw [hS]
    ext i j
    simp [mul_apply]
  have h4 : (Y.map Complex.ofReal).PosSemidef := by rw [h3]; exact posSemidef_conjTranspose_mul_self _
  refine h4.posDef_iff_det_ne_zero.2 ?_
  have h5 := Complex.ofRealHom.map_det Y
  rw [RingHom.mapMatrix_apply] at h5
  have h6 : (Y.map Complex.ofReal).det = (Y.det : ℂ) := h5.symm
  rw [h6]
  exact_mod_cast hY.det_pos.ne'

theorem inv_map_ofReal {Y : Matrix (Fin k) (Fin k) ℝ} (hY : Y.PosDef) :
    Y⁻¹.map Complex.ofReal = (Y.map Complex.ofReal)⁻¹ := by
  symm
  refine inv_eq_left_inv ?_
  have h := Matrix.map_mul (L := Y⁻¹) (M := Y) (f := Complex.ofRealHom)
  rw [nonsing_inv_mul _ (IsUnit.mk0 _ hY.det_pos.ne'), Matrix.map_one _ (map_zero _) (map_one _)] at h
  exact h.symm

theorem analyticAt_det {m : ℕ} {A : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ} {t : Fin n → ℂ}
    (h : ∀ p q, AnalyticAt ℂ (fun u => A u p q) t) : AnalyticAt ℂ (fun u => (A u).det) t := by
  simp only [det_apply']
  exact Finset.analyticAt_fun_sum _ fun σ _ => analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => h _ _)

theorem analyticAt_inv {A : (Fin n → ℂ) → Matrix (Fin k) (Fin k) ℂ} {t : Fin n → ℂ}
    (h : ∀ p q, AnalyticAt ℂ (fun u => A u p q) t) (h0 : (A t).det ≠ 0) (p q : Fin k) :
    AnalyticAt ℂ (fun u => (A u)⁻¹ p q) t := by
  simp only [inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul, adjugate_apply]
  refine ((analyticAt_det h).inv h0).mul (analyticAt_det fun i j => ?_)
  simp only [updateRow_apply]
  split_ifs
  · exact analyticAt_const
  · exact h _ _

theorem psh_core {τ : (Fin n → ℂ) → Matrix (Fin k) (Fin k) ℂ} {V : (Fin n → ℂ) → Matrix (Fin r) (Fin k) ℂ}
    {f : (Fin n → ℂ) → ℝ} (d : ℝ) (hτ : ∀ p q, AnalyticAt ℂ (fun u => τ u p q) 0)
    (hV : ∀ p q, AnalyticAt ℂ (fun u => V u p q) 0) (hV0 : Function.Injective (V 0).vecMul)
    (hpos : ∀ᶠ u in 𝓝 0, ((τ u).map Complex.im).PosDef) (hf : ContDiffAt ℝ 2 f 0)
    (he : ∀ᶠ u in 𝓝 0, (V u * (((τ u).map Complex.im).map Complex.ofReal)⁻¹ * (V u)ᴴ).PosDef →
      f u = d + Real.log (V u * (((τ u).map Complex.im).map Complex.ofReal)⁻¹ * (V u)ᴴ).det.re) : PshAt0 f := by
  obtain ⟨Y, hY⟩ : ∃ Y : (Fin n → ℂ) → Matrix (Fin k) (Fin k) ℂ,
      ∀ u, Y u = ((τ u).map Complex.im).map Complex.ofReal := ⟨_, fun _ => rfl⟩
  simp only [← hY] at he
  have hYp : ∀ᶠ u in 𝓝 0, (Y u).PosDef := hpos.mono fun u hu => by rw [hY]; exact posDef_ofReal hu
  have hY0 := hYp.self_of_nhds
  have huY : IsUnit (Y 0).det := IsUnit.mk0 _ hY0.det_pos.ne'
  obtain ⟨C, hC⟩ : ∃ C, C = (Y 0)⁻¹ * (V 0)ᴴ := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = V 0 * (Y 0)⁻¹ * (V 0)ᴴ := ⟨_, rfl⟩
  have hGp : G.PosDef := by rw [hG]; exact hY0.inv.mul_mul_conjTranspose_same hV0
  have huG : IsUnit G.det := IsUnit.mk0 _ hGp.det_pos.ne'
  have hVC : V 0 * C = G := by rw [hC, hG, Matrix.mul_assoc]
  have hM0 : Cᴴ * Y 0 * C = G := by
    rw [hC, hG, conjTranspose_mul, conjTranspose_conjTranspose, hY0.inv.1.eq]
    simp only [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ huY]
  have hCi : Function.Injective C.mulVec := by
    have h1 : Function.Injective G.mulVec :=
      Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 huG)
    intro x y hxy
    apply h1
    rw [← hVC, ← mulVec_mulVec, ← mulVec_mulVec, hxy]
  have hF : AnalyticAt ℂ (fun u => (V u * C).det) 0 := analyticAt_det fun p q => by
    simp only [mul_apply]
    exact Finset.analyticAt_fun_sum _ fun i _ => (hV _ _).mul analyticAt_const
  have hF0 : (V 0 * C).det ≠ 0 := by rw [hVC]; exact huG.ne_zero
  obtain ⟨Km, hK⟩ : ∃ Km, Km = C * G⁻¹ * Cᴴ := ⟨_, rfl⟩
  have hT : AnalyticAt ℂ (fun u => ∑ p, ∑ q, ((Km p q).re : ℂ) * (Complex.I * τ u q p)) 0 :=
    Finset.analyticAt_fun_sum _ fun p _ => Finset.analyticAt_fun_sum _ fun q _ =>
      analyticAt_const.mul (analyticAt_const.mul (hτ _ _))
  have htr : ∀ u, (∑ p, ∑ q, ((Km p q).re : ℂ) * (Complex.I * τ u q p)).re = -(G⁻¹ * (Cᴴ * Y u * C)).trace.re := by
    intro u
    have e : (G⁻¹ * (Cᴴ * Y u * C)).trace = (Km * Y u).trace := by
      rw [hK, ← Matrix.mul_assoc, trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [e, hY]
    simp [trace, mul_apply, Complex.re_sum]
  have hg := padd (plog_norm 2 (d - Real.log G.det.re + r) hF hF0) (pre hT)
  refine ptouch hf hg ?_ ?_
  · rw [he.self_of_nhds (hG ▸ hGp), htr, hM0, hVC, ← hG, nonsing_inv_mul _ huG, trace_one]
    have : ‖G.det‖ = G.det.re := by
      rw [det_eq_re hGp, Complex.norm_real, Complex.ofReal_re, Real.norm_of_nonneg (det_re_pos hGp).le]
    rw [this]
    simp
    ring
  · filter_upwards [he, hYp, hF.continuousAt.eventually_ne hF0] with u h1 h2 h3
    have hN : Cᴴ * (V u)ᴴ = (V u * C)ᴴ := (conjTranspose_mul _ _).symm
    have hVi : Function.Injective (V u).vecMul := by
      have h4 : Function.Injective (V u * C).vecMul :=
        Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 (IsUnit.mk0 _ h3))
      intro x y hxy
      apply h4
      have hxy' : x ᵥ* V u = y ᵥ* V u := hxy
      show x ᵥ* (V u * C) = y ᵥ* (V u * C)
      rw [← vecMul_vecMul, ← vecMul_vecMul, hxy']
    have hGu := h2.inv.mul_mul_conjTranspose_same hVi
    have hM := h2.conjTranspose_mul_mul_same hCi
    have a1 := logdet_dual_ge h2 (V u)ᴴ C hM (by rwa [conjTranspose_conjTranspose])
      (by rw [hN, det_conjTranspose]; exact star_ne_zero.2 h3)
    rw [hN, det_conjTranspose, norm_star, conjTranspose_conjTranspose] at a1
    have a2 := logdet_le hM hGp
    rw [h1 hGu, htr]
    linarith

end AnalyticReference.An.H
