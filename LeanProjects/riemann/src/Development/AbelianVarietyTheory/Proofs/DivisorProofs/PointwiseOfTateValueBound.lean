import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelLevelPPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelLevelPPowerTangentStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem ptSt_of_steps : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → TateSt → ValueSt → BoundSt → PtSt := by
  intro hK hT hV hB E _ _ _ H Dw τ p _ _ hs
  have hpos : (0 : ℝ) < ‖((((discr E : ℤ) : ℂ_[p]) ^ 2 * (p : ℂ_[p]) ^ 2) ^ (Dw.mult τ.1 + Dw.mult (conjEmb τ.1)))‖ := by
    refine norm_pos_iff.2 (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ ?_) (pow_ne_zero _ ?_)))
    · exact Int.cast_ne_zero.2 (NumberField.discr_ne_zero E)
    · exact Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos hp1
  refine ⟨n, ?_⟩
  intro l l' Xo Xo' c c' W Y r ν hle hOI hA N a T S hLat _ f yb yy P π ψ y hHT hf
  obtain ⟨κ, hκ, hcl⟩ := GlobalTheory.T.integral_model_level_p_power_tangent hK hT hV hB E H Dw τ p hs n l l' Xo Xo' c c' W Y r ν hle hOI hA N a T S hLat f
    yb yy P π ψ y hHT hf
  exact ⟨κ, hκ, fun β hβ g e U₁ U₂ h h1 h2 h3 h4 =>
    ⟨GlobalTheory.T.integral_model_level_p_power hK hT hV hB E H Dw τ p hs n l l' Xo Xo' c c' W Y r ν hle hOI hA N a T S hLat f yb yy P π ψ y hHT hn
      β hβ g e U₁ U₂ h h1 h2 h3 h4, hcl β hβ g e U₁ U₂ h h1 h2 h3 h4⟩⟩

end GlobalTheory.FlatModel
