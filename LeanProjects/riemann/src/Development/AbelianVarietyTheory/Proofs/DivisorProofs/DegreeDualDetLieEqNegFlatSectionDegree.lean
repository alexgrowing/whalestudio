import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatSectionValueEqMulDetInvStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionValuationAtFinitePlaceEqSubDetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantNormFlatSectionEqNormDivNormDetStatement

noncomputable section

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

namespace GlobalTheory.DefPt

theorem degLie_eq_neg_deg_flat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z), (∀ (τ : Psi H) (s : FlatSec U ξ Z τ), P.degLie τ.1 = -s.deg) ∧ ∀ τ : E →+* ℂ, τ (H.rt : E) ≠ H.rt0 → Dw.mult τ = 0 := by
  intro E _ _ _ H Dw l Xo c r U ξ hD Z P
  refine ⟨fun τ s => ?_, fun τ h => ?_⟩
  · obtain ⟨b, hb0, hb⟩ := GlobalTheory.T.exists_flatSectionValue_eq_mul_det_inv E H Dw l Xo c r U ξ hD Z P τ s
    have h2 := GlobalTheory.T.flatSection_valuation_at_finitePlace_eq_sub_det E H Dw l Xo c r U ξ hD Z P τ s b hb0 hb
    have h3 := GlobalTheory.T.constantNorm_flatSection_eq_norm_div_norm_det E H Dw l Xo c r U ξ hD Z P τ s b hb0 hb
    have hX : ∀ σ, 0 < ‖(P.X σ τ.1).det‖ := fun σ => norm_pos_iff.2 ((P.arch σ).2.1 τ.1)
    have hfB : (Function.support fun w => (vAdd w (P.B w τ.1).det : ℝ)).Finite := by
      have e : (fun w => (vAdd w (P.B w τ.1).det : ℝ)) = (fun w => (vAdd w b : ℝ)) - s.rho_vw := by
        funext w; rw [Pi.sub_apply, h2 w]; ring
      rw [e]
      exact ((finite_vAdd hb0).union s.finite_rho).subset (Function.support_sub _ _)
    have hm := lineDeg_mul (r := fun σ => ‖(P.X σ τ.1).det‖) (r' := s.cInf) hX s.cInf_pos hfB s.finite_rho
    have e1 : ((fun σ => ‖(P.X σ τ.1).det‖) * s.cInf) = fun σ : c.F →+* ℂ => ‖σ b‖ := by
      funext σ; rw [Pi.mul_apply, h3 σ]; field_simp [(hX σ).ne']
    have e2 : ((fun w => (vAdd w (P.B w τ.1).det : ℝ)) + s.rho_vw) = fun w => (vAdd w b : ℝ) := by
      funext w; rw [Pi.add_apply, h2 w]; ring
    rw [e1, e2, lineDeg_num hb0] at hm
    have : P.degLie τ.1 + s.deg = 0 := by
      rw [hm]; rfl
    linarith
  · have hq : Dw.q = 0 := hD.q
    simp only [Datum.mult, if_neg h, hq]

end GlobalTheory.DefPt

end
