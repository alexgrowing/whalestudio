import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefSectionGrowth

theorem isProjOver_strHom {F : Type} [Field F] (Y : Var F) : IsProjOver (strHom F Y.X) := by
  rw [strHom_eq Y.algebraMap_Γ]
  exact Y.isProjOver

theorem toENat_rank_H0_nsmul {F : Type} [Field F] (Y : Var F) (Δ : Y.Dv) (τ : ℕ) :
    Cardinal.toENat (Module.rank F (Y.H0 (τ • Δ))) = (lbH0 F (lbPow (Y.lb Δ) τ) : ℕ∞) := by
  rw [← Module.finrank_eq_rank, Var.finrank_riemannRoch_nsmul]
  simp

theorem growth_le_inter (hN : GlobalTheory.Published.NefNumerics) (F : Type) [Field F] [NumberField F] (Y : Var F)
    (Δ : Y.Dv) (hΔ : Y.nef Δ) :
    growth Y.dim (fun τ => Cardinal.toENat (Module.rank F (Y.H0 (τ • Δ)))) ≤
      ENNReal.ofReal (Y.inter fun _ => Δ : ℝ) := by
  have ht := hN.2.2.tendsto (isProjOver_strHom Y) Y.topologicalKrullDim_eq hΔ
  have hf : (0 : ℝ) < (Y.dim.factorial : ℝ) := by positivity
  have hi : ((Y.inter fun _ => Δ : ℤ) : ℝ) = (topSelfIntersection F (Y.lb Δ) Y.dim : ℝ) := by
    rw [topSelf_def]; rfl
  have h2 := ENNReal.tendsto_ofReal (ht.const_mul (Y.dim.factorial : ℝ))
  rw [mul_div_cancel₀ _ hf.ne', ← hi] at h2
  refine le_of_eq (Tendsto.limsup_eq (h2.congr' ?_))
  filter_upwards [eventually_gt_atTop 0] with τ hτ
  rw [toENat_rank_H0_nsmul, ENat.toENNReal_coe, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast, mul_div_assoc]

theorem growth_h0_le_self_intersection : GlobalTheory.Published.NefNumerics → ∀ (F : Type) [Field F] [NumberField F]
    (Y : Var F) (Δ : Y.Dv), Y.nef Δ → growth Y.dim (fun τ => Cardinal.toENat
      (Module.rank F (Y.H0 (τ • Δ)))) ≤ ENNReal.ofReal (Y.inter fun _ => Δ : ℝ) :=
  fun hN F _ _ Y Δ hΔ => growth_le_inter hN F Y Δ hΔ

end GlobalTheory.NefSectionGrowth
