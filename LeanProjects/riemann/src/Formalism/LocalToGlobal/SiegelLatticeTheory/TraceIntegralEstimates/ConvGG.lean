import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.ConvGOne

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

namespace Formalism.L2.S.Pv.ConvG

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.EnergyAbs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LocQuadGG_G : Prop :=
  ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ),
    0 < sc → ∀ (v : InfinitePlace X.B.I.F) (cv : Fin (D.R.rS + 1) → ℂ),
      cv ∈ Formalism.L2.SG.RealObj.EnergyCut.GoodV (D := D) u u' → ∀ g : Formalism.REAL.UJ (X.B.I.ε v),
        Zhat (X.B.I.ε v) (frm X u sc v) (frm X u' sc v) (uMat g) = Matrix.diagonal cv →
        ∫⁻ x, ∫⁻ y, ‖⟪X.B.σ v (uMat x) (X.B.w v), X.B.σ v (uMat g) (X.B.σ v (uMat y) (X.B.w v))⟫_ℂ‖ₑ *
          ‖X.Wloc u v x‖ₑ * ‖X.Wloc u' v y‖ₑ ∂(Formalism.REAL.muG (X.B.I.ε v)) ∂(Formalism.REAL.muG (X.B.I.ε v)) < ⊤

def LocQuad1_G : Prop :=
  ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : D.what₂.Word)
    (μS νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) (C : ℝ≥0∞),
    Formalism.L2.SG.Pf.WuDec.QuotWit X w μS νl C → ∀ v, ∫⁻ a, Kv X w v a ∂(νl v) < ⊤

def StepConvG : Prop :=
  ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ),
    0 < sc →
    (∀ c ∈ Good X u u', ∀ γ, HasDiag X u u' sc c γ →
      ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', ‖⟪X.B.σs z (X.B.tens X.B.w),
          X.B.σs (s * γ * s'⁻¹) (X.B.σs z' (X.B.tens X.B.w))⟫_ℂ‖ₑ * ‖X.Wu u z‖ₑ * ‖X.Wu u' z'‖ₑ
        ∂(muS X u') ∂(muS X u) ∂(X.nuQ u') ∂(X.nuQ u) < ⊤) ∧
    ∀ w : D.what₂.Word,
      ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪X.B.σs z (X.B.tens X.B.w), X.B.σs s (X.B.σs z' (X.B.tens X.B.w))⟫_ℂ‖ₑ *
        ‖X.Wu w z‖ₑ * ‖X.Wu w z'‖ₑ ∂(muS X w) ∂(X.nuQ w) ∂(X.nuQ w) < ⊤

theorem double_integral_finite_diagonal {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ) (hsc : 0 < sc)
    (hL : ∀ (v : InfinitePlace X.B.I.F) (cv : Fin (D.R.rS + 1) → ℂ),
      cv ∈ Formalism.L2.SG.RealObj.EnergyCut.GoodV (D := D) u u' → ∀ g : Formalism.REAL.UJ (X.B.I.ε v),
        Zhat (X.B.I.ε v) (frm X u sc v) (frm X u' sc v) (uMat g) = Matrix.diagonal cv →
        ∫⁻ x, ∫⁻ y, ‖⟪X.B.σ v (uMat x) (X.B.w v), X.B.σ v (uMat g) (X.B.σ v (uMat y) (X.B.w v))⟫_ℂ‖ₑ *
          ‖X.Wloc u v x‖ₑ * ‖X.Wloc u' v y‖ₑ ∂(Formalism.REAL.muG (X.B.I.ε v)) ∂(Formalism.REAL.muG (X.B.I.ε v)) < ⊤)
    (c : Cinf X) (hc : c ∈ Good X u u') (γ : X.B.I.Ginf) (hγ : HasDiag X u u' sc c γ) :
    ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', ‖⟪X.B.σs z (X.B.tens X.B.w),
        X.B.σs (s * γ * s'⁻¹) (X.B.σs z' (X.B.tens X.B.w))⟫_ℂ‖ₑ * ‖X.Wu u z‖ₑ * ‖X.Wu u' z'‖ₑ
      ∂(muS X u') ∂(muS X u) ∂(X.nuQ u') ∂(X.nuQ u) < ⊤ := by
  obtain ⟨hH, -, -, -, hsf⟩ := Formalism.L2.S.Pv.HaarSubS.stepSubG_holds D X u
  obtain ⟨hH', -, -, -, hsf'⟩ := Formalism.L2.S.Pv.HaarSubS.stepSubG_holds D X u'
  obtain ⟨-, -, -, hiS, hsig, -, h0, -, -, -, hinv⟩ := hH
  obtain ⟨-, -, -, hiS', hsig', -, h0', -, -, -, hinv'⟩ := hH'
  have := hsig
  have := hsig'
  have := hsf
  have := hsf'
  have hrep := (Formalism.L2.S.Pv.SchurTens.stepSchurG_holds D X).1
  rw [quad_eq_GG (μ := Formalism.L2.SG.ProjRows.muInf X.B.I) (μS := muS X u) (μS' := muS X u') hrep
    (X.B.tens X.B.w) (X.Wu_spec u).2.2.1 (X.Wu_spec u').2.2.1 (X.nuQ_weil u) (X.nuQ_weil u') hinv hinv' h0 h0'
    hiS hiS' (norm_Wu_S X u) (norm_Wu_S X u') γ, lint_GG_prod]
  refine ENNReal.prod_lt_top fun v _ => ?_
  unfold phiV
  exact hL v (c v) (hc v) (γ v) (hγ v)

theorem convolution_integral_finite {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : D.what₂.Word)
    (hC : ∀ (μS νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) (C : ℝ≥0∞),
      Formalism.L2.SG.Pf.WuDec.QuotWit X w μS νl C → ∀ v, ∫⁻ a, Kv X w v a ∂(νl v) < ⊤) :
    ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪X.B.σs z (X.B.tens X.B.w), X.B.σs s (X.B.σs z' (X.B.tens X.B.w))⟫_ℂ‖ₑ *
      ‖X.Wu w z‖ₑ * ‖X.Wu w z'‖ₑ ∂(muS X w) ∂(X.nuQ w) ∂(X.nuQ w) < ⊤ := by
  obtain ⟨μSl, νl, C, hQ⟩ := Formalism.L2.SG.Pf.WuDec.quotAll_of Formalism.L2.SG.Closed.QuotProdK_holds
    Formalism.L2.SG.Pf.WFL.locHNProps_holds Formalism.L2.SG.Closed.NUnimodLoc_holds D X w
  have hQ' := hQ
  obtain ⟨hC0, hCt, -, hprod⟩ := hQ'
  simp only [inner_weil X w, K_eq X w]
  rw [hprod (fun v => Kv X w v) (fun v => measurable_Kv X w v)
    (fun v m hm h hh x => Kv_inv X w v m hm h hh x)]
  exact ENNReal.mul_lt_top (lt_of_le_of_ne le_top hCt) (ENNReal.prod_lt_top fun v _ => hC μSl νl C hQ v)

theorem stepConvG_of (hB : LocQuadGG_G) (hC : LocQuad1_G) : StepConvG := by
  intro D hG X u u' sc hsc
  exact ⟨fun c hc γ hγ => double_integral_finite_diagonal X u u' sc hsc (hB D hG X u u' sc hsc) c hc γ hγ,
    fun w => convolution_integral_finite X w (hC D hG X w)⟩

end Formalism.L2.S.Pv.ConvG
