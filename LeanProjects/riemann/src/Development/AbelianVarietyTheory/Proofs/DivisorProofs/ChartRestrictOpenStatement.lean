import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartRestrictOpen
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelOpenNoetherian

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_restrict_open : ∀ (p n : ℕ) [Fact p.Prime] (X : Scheme.{0}) (U Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p])
    (x : U.toScheme), ChartAt p n Xw K (U.ι x) → ChartAt p n (U.ι ⁻¹ᵁ Xw) (fun yb => K (yb ≫ U.ι)) x := by
  first | exact @GlobalTheory.FlatModel.chartAt_opens_restrict | exact GlobalTheory.FlatModel.chartAt_opens_restrict | (intros; apply GlobalTheory.FlatModel.chartAt_opens_restrict <;> assumption)
