import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaProd
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProd
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory NumberField
open Limits MonoidalCategory CartesianMonoidalCategory GlobalTheory.VB
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasTheta_of_isProd' : ∀ (S : Scheme.{0}) (P P₁ P₂ : PPAS S), P.IsProd P₁ P₂ → P₁.HasTheta → P₂.HasTheta → P.HasTheta := by
  first | exact @GlobalTheory.PPAS.hasTheta_prod | exact GlobalTheory.PPAS.hasTheta_prod | (intros; apply GlobalTheory.PPAS.hasTheta_prod <;> assumption)
