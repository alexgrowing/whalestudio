import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensityStatementHoldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictionStatementHoldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularityOfDensityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalOfConnectedDensityStatement

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

theorem glueSt_of (hC : ConnSt) (hZ : GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.PropZ) : GlueSt := by
  intro F _ _ V p _ hp X s Xw hN hP hF hXw hG n K hK hCh
  obtain ⟨X₁, s₁, Xw₁, K₁, hI₁, hN₁, hP₁, hF₁, hXw₁, hG₁, hK₁, hCh₁, hT₁⟩ :=
    GlobalTheory.T.restriction_statement_holds F V p hp X s Xw hN hP hF hXw hG n K hK hCh
  obtain ⟨X₂, s₂, Xw₂, K₂, hI₂, hN₂, hP₂, hF₂, hXw₂, hG₂, hK₂, hCh₂, hT₂⟩ :=
    GlobalTheory.T.modularity_of_density GlobalTheory.T.density_statement_holds F V p hp X₁ s₁ Xw₁ hI₁ hN₁ hP₁ hF₁ hXw₁ hG₁ n K₁ hK₁ hCh₁
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.principal_of_connected_density hC hZ GlobalTheory.T.density_statement_holds F V p hp X₂ s₂ Xw₂ hI₂ hN₂ hP₂ hF₂ hXw₂ hG₂ K₂ hK₂ hCh₂
  refine ⟨ρ, fun yb hyb κ hκ => ?_⟩
  obtain ⟨yb₁, h1, hs1⟩ := hT₁ yb hyb
  obtain ⟨yb₂, h2, hs2⟩ := hT₂ yb₁ h1
  exact hρ yb₂ h2 κ (hs2 (hs1 hκ))

end GlobalTheory.FlatModel
