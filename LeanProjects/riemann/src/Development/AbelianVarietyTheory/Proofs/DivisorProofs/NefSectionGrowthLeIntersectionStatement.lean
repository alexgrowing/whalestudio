import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefSectionGrowthLeIntersection
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nef_section_growth_le_intersection : GlobalTheory.Published.NefNumerics → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (Δ : Y.Dv), Y.nef Δ → growth Y.dim (fun τ => Cardinal.toENat (Module.rank F (Y.H0 (τ • Δ)))) ≤ ENNReal.ofReal (Y.inter fun _ => Δ : ℝ) := by
  first | exact @GlobalTheory.NefSectionGrowth.growth_h0_le_self_intersection | exact GlobalTheory.NefSectionGrowth.growth_h0_le_self_intersection | (intros; apply GlobalTheory.NefSectionGrowth.growth_h0_le_self_intersection <;> assumption)
