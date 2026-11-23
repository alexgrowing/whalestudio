import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasConesIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeAtOfToricChartStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeAtInteriorPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricChartsGlobalConditionsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricChartsPolarizedModelStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GenFan

theorem genFanSt_of_toroidalCharts (hP : GlobalTheory.Published.ToroidalChartsForFan) : GenFanSt := by
  intro E _ _ _ H D hr φ h₁ h₂ l Xo c
  obtain ⟨Y, BD, d, k, hd, -, hsm, hsnc, hsupp, hch, ha⟩ := hP E H D hr φ h₁ h₂ l Xo c
  refine ⟨Y, BD, d, k, hd, ⟨hsm, hsnc, fun x hx => ?_⟩, (hasCones_iff _ _).2 fun z => ?_,
    GlobalTheory.T.toric_charts_global_conditions φ h₁ h₂ Y BD d hsm hsnc hsupp hch, ha (GlobalTheory.T.toric_charts_polarized_model φ Y BD d hr hsm hsnc hsupp hch)⟩
  · obtain ⟨k, _, m, e, ξ, t, P, γ, -, -, hx', htc, -⟩ := (hch x hx).exists_isToricChart
    exact ⟨k, _, m, e, ξ, t, P, γ, hx', htc⟩
  · rcases exists_of_id Y z with ⟨x, hx, rfl⟩ | ⟨w, rfl⟩
    · exact GlobalTheory.T.coneAt_of_toric_chart φ Y BD d x (hch x hx)
    · exact GlobalTheory.T.coneAt_interior_point φ Y w

end GlobalTheory.GenFan
