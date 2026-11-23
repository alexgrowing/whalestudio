import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Formalism.HarderNarasimhan.StatementPl
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopRankPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulBoundAtOfNotIsReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulBoundAtBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HilbertSamuel.Data

theorem complexify_statement : Complexify := by
  intro F _ _ X β hF _ hS hB
  haveI := hF
  exact ⟨fun σ => hB.mulBoundAt σ, fun E _ _ _ => hS.baseChange E⟩

end GlobalTheory.HilbertSamuel.Data
